module

public import OddPerfect.DeficientReplay5.Part007

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour5Part035Tree : Tree :=
  .step (.primeLo 3 4621) <|
  .step (.dropHi 4 269) <|
  .splitBase 3 5539
    (.step (.primeHi 3 5531) <|
    .step (.dropLo 4 263) <|
    .step (.xLo 265) <|
    .splitExp 0 8
      (.missing 0 13)
      (.step (.dropLo 4 267) <|
      .step (.xLo 269) <|
      .step (.dropHi 3 4918) <|
      .step (.primeHi 3 4909) <|
      .splitExp 1 6
        (.step (.dropHi 3 4627) <|
        .step (.primeHi 3 4621) <|
        .splitExp 0 10
          (.missing 0 23)
          (.splitExp 2 4
            (.reject)
            (.splitExp 0 12
              (.reject)
              (.reject))))
        (.step (.dropLo 3 4758) <|
        .step (.primeLo 3 4759) <|
        .splitExp 0 10
          (.missing 0 23)
          (.step (.dropLo 3 4874) <|
          .step (.primeLo 3 4877) <|
          .splitBase 3 4891
            (.step (.primeHi 3 4889) <|
            .splitExp 2 4
              (.splitExp 0 12
                (.step (.dropHi 3 4886) <|
                .step (.primeHi 3 4877) <|
                .splitExp 1 8
                  (.missing 1 19)
                  (.reject))
                (.step (.dropLo 3 4887) <|
                .step (.primeLo 3 4889) <|
                .splitExp 1 8
                  (.missing 1 19)
                  (.reject)))
              (.reject))
            (.step (.primeLo 3 4903) <|
            .splitExp 2 4
              (.reject)
              (.splitExp 0 12
                (.step (.dropHi 3 4903) <|
                .splitExp 1 8
                  (.missing 1 19)
                  (.reject))
                (.step (.dropLo 3 4904) <|
                .step (.primeLo 3 4909) <|
                .splitExp 1 8
                  (.missing 1 19)
                  (.reject))))))))
    (.step (.primeLo 3 5557) <|
    .step (.dropHi 4 267) <|
    .step (.xHi 265) <|
    .splitExp 0 8
      (.missing 0 13)
      (.step (.dropLo 3 6004) <|
      .step (.dropLo 4 264) <|
      .step (.primeLo 3 6007) <|
      .step (.xLo 265) <|
      .missing 4 7))

theorem deficientFour5Part035 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,4618,6917,2,0⟩, ⟨true,261,273,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part035Tree [] _ _ (by decide +kernel)

private def deficientFour5Part036Tree : Tree :=
  .step (.primeLo 3 863) <|
  .step (.dropHi 4 362) <|
  .step (.xHi 361) <|
  .splitBase 3 1725
    (.step (.primeHi 3 1723) <|
    .step (.dropLo 4 232) <|
    .step (.xLo 233) <|
    .splitExp 0 6
      (.step (.fix 0 1093 3) <|
      .step (.dropLo 4 251) <|
      .step (.dropHi 4 288) <|
      .step (.xLo 253) <|
      .step (.xHi 285) <|
      .splitExp 1 4
        (.step (.grow 1 11) <|
        .missing 1 71)
        (.step (.dropLo 4 272) <|
        .step (.xLo 273) <|
        .splitExp 2 2
          (.missing 2 307)
          (.reject)))
      (.use 0))
    (.step (.primeLo 3 1733) <|
    .step (.dropHi 4 299) <|
    .step (.xHi 297) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 4 223) <|
      .step (.xLo 225) <|
      .splitBase 3 3465
        (.use 1)
        (.step (.primeLo 3 3467) <|
        .step (.dropHi 4 275) <|
        .step (.xHi 273) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .missing 1 71)
          (.step (.dropLo 4 239) <|
          .step (.xLo 241) <|
          .splitBase 3 6933
            (.step (.primeHi 3 6917) <|
            .step (.dropLo 4 248) <|
            .step (.xLo 249) <|
            .splitExp 2 2
              (.missing 2 307)
              (.step (.dropLo 4 261) <|
              .splitBase 3 4617
                (.step (.primeHi 3 4603) <|
                .step (.dropLo 4 266) <|
                .step (.xLo 269) <|
                .splitBase 3 3955
                  (.step (.primeHi 3 3947) <|
                  .splitExp 0 8
                    (.step (.grow 0 13) <|
                    .missing 0 757)
                    (.step (.dropLo 3 3614) <|
                    .step (.dropLo 4 272) <|
                    .step (.primeLo 3 3617) <|
                    .step (.xLo 273) <|
                    .missing 4 137))
                  (.step (.primeLo 3 3967) <|
                  .step (.dropHi 4 272) <|
                  .step (.xHi 269) <|
                  .splitExp 0 8
                    (.missing 0 13)
                    (.step (.dropLo 3 4495) <|
                    .step (.primeLo 3 4507) <|
                    .splitExp 1 6
                      (.splitExp 0 10
                        (.missing 0 23)
                        (.step (.dropLo 3 4599) <|
                        .step (.primeLo 3 4603) <|
                        .splitExp 2 4
                          (.splitExp 0 12
                            (.reject)
                            (.reject))
                          (.reject)))
                      (.reject))))
                (.use 2)))
            (.step (.primeLo 3 6947) <|
            .step (.dropHi 4 264) <|
            .step (.xHi 261) <|
            .splitExp 2 2
              (.missing 2 307)
              (.step (.dropLo 4 251) <|
              .step (.xLo 253) <|
              .splitBase 3 13893
                (.step (.primeHi 3 13883) <|
                .step (.dropLo 4 256) <|
                .step (.xLo 257) <|
                .splitBase 3 9259
                  (.step (.primeHi 3 9257) <|
                  .step (.dropLo 4 258) <|
                  .step (.xLo 261) <|
                  .missing 4 131)
                  (.step (.primeLo 3 9277) <|
                  .splitExp 0 8
                    (.missing 0 13)
                    (.step (.dropLo 4 259) <|
                    .step (.xLo 261) <|
                    .missing 4 131)))
                (.step (.primeLo 3 13901) <|
                .step (.dropHi 4 259) <|
                .step (.xHi 257) <|
                .splitBase 3 27801
                  (.step (.primeHi 3 27799) <|
                  .step (.dropLo 4 254) <|
                  .step (.xLo 257) <|
                  .missing 4 43)
                  (.step (.primeLo 3 27803) <|
                  .splitExp 0 8
                    (.missing 0 13)
                    (.step (.dropLo 4 254) <|
                    .step (.xLo 257) <|
                    .missing 4 43)))))))))

private def deficientFour5Part036Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,863,1723,2,0⟩, ⟨true,233,361,1,1⟩], 1, deficientFour5Part033⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,1733,3465,2,0⟩, ⟨true,225,297,1,1⟩], 1, deficientFour5Part034⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,4618,6917,2,0⟩, ⟨true,261,273,1,1⟩], 1, deficientFour5Part035⟩]

theorem deficientFour5Part036 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,862,0,2,0⟩, ⟨true,205,625,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part036Tree deficientFour5Part036Refs _ _ (by decide +kernel)

private def deficientFour5Part037Tree : Tree :=
  .step (.dropLo 4 117) <|
  .splitExp 0 4
    (.step (.grow 0 11) <|
    .step (.dropHi 4 338) <|
    .step (.xLo 121) <|
    .step (.xHi 297) <|
    .splitBase 3 393
      (.step (.primeHi 3 389) <|
      .step (.dropLo 4 167) <|
      .step (.xLo 209) <|
      .step (.dropHi 3 306) <|
      .step (.primeHi 3 293) <|
      .splitBase 3 235
        (.step (.primeHi 3 233) <|
        .step (.dropLo 4 235) <|
        .step (.xLo 253) <|
        .splitBase 3 213
          (.step (.primeHi 3 211) <|
          .step (.dropLo 4 262) <|
          .step (.xLo 297) <|
          .missing 4 149)
          (.step (.primeLo 3 223) <|
          .step (.dropHi 4 281) <|
          .step (.xHi 253) <|
          .missing 4 127))
        (.step (.primeLo 3 239) <|
        .step (.dropHi 4 259) <|
        .step (.xHi 253) <|
        .splitBase 3 263
          (.step (.dropLo 4 210) <|
          .step (.xLo 253) <|
          .missing 4 127)
          (.step (.primeLo 3 269) <|
          .step (.dropHi 4 231) <|
          .step (.xHi 209) <|
          .missing 4 7)))
      (.step (.primeLo 3 397) <|
      .step (.dropHi 4 180) <|
      .step (.xHi 165) <|
      .splitBase 3 793
        (.step (.primeHi 3 787) <|
        .step (.dropLo 4 137) <|
        .step (.xLo 165) <|
        .missing 4 83)
        (.step (.primeLo 3 797) <|
        .step (.dropHi 4 146) <|
        .step (.xHi 121) <|
        .missing 4 61)))
    (.step (.dropLo 3 204) <|
    .step (.dropLo 4 204) <|
    .step (.primeLo 3 211) <|
    .step (.xLo 205) <|
    .splitBase 3 421
      (.use 0)
      (.step (.primeLo 3 431) <|
      .step (.dropHi 4 628) <|
      .step (.xHi 625) <|
      .splitBase 3 861
        (.step (.primeHi 3 859) <|
        .step (.dropLo 4 268) <|
        .step (.xLo 269) <|
        .splitBase 3 573
          (.step (.primeHi 3 571) <|
          .step (.dropLo 4 318) <|
          .step (.xLo 321) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 366) <|
            .step (.xLo 369) <|
            .splitBase 3 491
              (.step (.dropLo 4 408) <|
              .step (.xLo 409) <|
              .splitExp 1 4
                (.step (.grow 1 11) <|
                .missing 1 71)
                (.step (.dropLo 4 467) <|
                .step (.xLo 469) <|
                .splitBase 3 459
                  (.use 1)
                  (.step (.primeLo 3 461) <|
                  .step (.dropHi 4 573) <|
                  .splitExp 2 2
                    (.missing 2 307)
                    (.step (.dropLo 4 516) <|
                    .step (.xLo 517) <|
                    .splitBase 3 475
                      (.step (.primeHi 3 467) <|
                      .step (.dropLo 4 545) <|
                      .splitExp 0 8
                        (.missing 0 13)
                        (.step (.dropLo 4 559) <|
                        .step (.xLo 561) <|
                        .splitBase 3 463
                          (.step (.dropLo 4 565) <|
                          .splitExp 1 6
                            (.step (.dropHi 4 569) <|
                            .splitBase 3 461
                              (.step (.dropLo 4 568) <|
                              .step (.xLo 569) <|
                              .missing 4 19)
                              (.step (.primeLo 3 463) <|
                              .step (.dropHi 4 566) <|
                              .step (.xHi 565) <|
                              .missing 4 283))
                            (.step (.dropLo 4 569) <|
                            .splitBase 3 461
                              (.step (.dropLo 4 572) <|
                              .step (.xLo 573) <|
                              .missing 4 7)
                              (.step (.primeLo 3 463) <|
                              .step (.dropHi 4 570) <|
                              .step (.xHi 569) <|
                              .missing 4 19)))
                          (.step (.primeLo 3 467) <|
                          .step (.dropHi 4 564) <|
                          .step (.xHi 561) <|
                          .missing 4 281)))
                      (.step (.primeLo 3 479) <|
                      .step (.dropHi 4 547) <|
                      .step (.xHi 545) <|
                      .splitExp 0 8
                        (.step (.grow 0 13) <|
                        .missing 0 757)
                        (.step (.dropLo 4 528) <|
                        .step (.xLo 529) <|
                        .splitBase 3 483
                          (.step (.primeHi 3 479) <|
                          .step (.dropLo 4 543) <|
                          .step (.xLo 545) <|
                          .missing 4 7)
                          (.step (.primeLo 3 487) <|
                          .step (.dropHi 4 537) <|
                          .splitExp 1 6
                            (.step (.dropHi 4 533) <|
                            .splitBase 3 487
                              (.step (.dropLo 4 533) <|
                              .missing 4 89)
                              (.step (.primeLo 3 491) <|
                              .step (.dropHi 4 529) <|
                              .missing 4 53))
                            (.step (.dropLo 4 531) <|
                            .step (.xLo 533) <|
                            .step (.dropHi 3 490) <|
                            .step (.primeHi 3 487) <|
                            .step (.dropLo 4 536) <|
                            .step (.xLo 537) <|
                            .missing 4 269))))))))
              (.use 2)))
          (.use 3))
        (.use 4)))

private def deficientFour5Part037Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,211,421,2,0⟩, ⟨true,205,0,1,1⟩], 1, deficientFour5Part026⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,431,459,2,0⟩, ⟨true,469,625,1,1⟩], 1, deficientFour5Part027⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,492,571,2,0⟩, ⟨true,369,625,1,1⟩], 1, deficientFour5Part028⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,574,859,2,0⟩, ⟨true,269,625,1,1⟩], 1, deficientFour5Part030⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,862,0,2,0⟩, ⟨true,205,625,1,1⟩], 1, deficientFour5Part036⟩]

theorem deficientFour5Part037 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,197,0,2,0⟩, ⟨true,69,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part037Tree deficientFour5Part037Refs _ _ (by decide +kernel)

private def deficientFour5Part038Tree : Tree :=
  .step (.primeHi 3 257) <|
  .step (.dropLo 4 133) <|
  .splitBase 3 223
    (.step (.dropLo 4 145) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 4 154) <|
      .step (.xLo 157) <|
      .splitBase 3 209
        (.step (.primeHi 3 199) <|
        .step (.dropLo 4 168) <|
        .step (.xLo 169) <|
        .splitExp 1 4
          (.missing 1 11)
          (.step (.dropLo 4 177) <|
          .splitExp 2 2
            (.missing 2 127)
            (.step (.dropLo 4 182) <|
            .step (.xLo 185) <|
            .missing 4 31)))
        (.step (.primeLo 3 211) <|
        .step (.dropHi 4 174) <|
        .step (.xHi 173) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .missing 1 71)
          (.step (.dropLo 4 162) <|
          .step (.xLo 165) <|
          .splitBase 3 215
            (.step (.primeHi 3 211) <|
            .step (.dropLo 4 169) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 173) <|
              .missing 4 29))
            (.step (.primeLo 3 223) <|
            .step (.dropHi 4 166) <|
            .step (.xHi 165) <|
            .missing 4 83)))))
    (.step (.primeLo 3 227) <|
    .step (.dropHi 4 164) <|
    .step (.xHi 161) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 4 141) <|
      .splitBase 3 241
        (.step (.dropLo 4 146) <|
        .step (.xLo 149) <|
        .splitExp 1 4
          (.missing 1 11)
          (.step (.dropLo 4 153) <|
          .splitBase 3 233
            (.step (.dropLo 4 157) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 3 230) <|
              .step (.dropLo 4 160) <|
              .step (.primeLo 3 233) <|
              .step (.xLo 161) <|
              .splitExp 0 8
                (.missing 0 13)
                (.reject)))
            (.step (.primeLo 3 239) <|
            .step (.dropHi 4 158) <|
            .step (.xHi 157) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 157) <|
              .missing 4 79))))
        (.step (.primeLo 3 251) <|
        .step (.dropHi 4 153) <|
        .splitExp 1 4
          (.missing 1 11)
          (.step (.dropLo 4 147) <|
          .step (.xLo 149) <|
          .splitExp 2 2
            (.missing 2 127)
            (.step (.dropLo 4 151) <|
            .step (.xLo 153) <|
            .missing 4 7)))))

theorem deficientFour5Part038 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,197,261,2,0⟩, ⟨true,113,185,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part038Tree [] _ _ (by decide +kernel)

private def deficientFour5Part039Tree : Tree :=
  .step (.primeHi 3 389) <|
  .step (.dropLo 4 113) <|
  .splitBase 3 261
    (.use 0)
    (.step (.primeLo 3 263) <|
    .step (.dropHi 4 149) <|
    .splitBase 3 313
      (.step (.dropLo 4 122) <|
      .step (.xLo 125) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.step (.dropLo 4 128) <|
        .step (.xLo 129) <|
        .splitBase 3 285
          (.step (.primeHi 3 283) <|
          .step (.dropLo 4 134) <|
          .step (.xLo 137) <|
          .splitExp 1 4
            (.missing 1 11)
            (.step (.dropLo 4 140) <|
            .step (.xLo 141) <|
            .splitBase 3 271
              (.step (.dropLo 4 143) <|
              .step (.xLo 145) <|
              .splitExp 2 2
                (.missing 2 127)
                (.step (.dropLo 4 146) <|
                .step (.xLo 149) <|
                .step (.dropHi 3 264) <|
                .step (.primeHi 3 263) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.reject)))
              (.step (.primeLo 3 277) <|
              .step (.dropHi 4 145) <|
              .splitExp 2 2
                (.missing 2 127)
                (.step (.dropLo 4 143) <|
                .step (.xLo 145) <|
                .missing 4 73))))
          (.step (.primeLo 3 293) <|
          .step (.dropHi 4 141) <|
          .splitExp 1 4
            (.missing 1 11)
            (.step (.dropLo 4 134) <|
            .step (.xLo 137) <|
            .splitBase 3 301
              (.step (.primeHi 3 293) <|
              .step (.dropLo 4 138) <|
              .step (.xLo 141) <|
              .missing 4 71)
              (.step (.primeLo 3 307) <|
              .step (.dropHi 4 138) <|
              .step (.xHi 137) <|
              .missing 4 23)))))
      (.step (.primeLo 3 317) <|
      .step (.dropHi 4 136) <|
      .step (.xHi 133) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.step (.dropLo 4 119) <|
        .step (.xLo 121) <|
        .splitBase 3 349
          (.step (.dropLo 4 123) <|
          .step (.xLo 125) <|
          .splitExp 1 4
            (.missing 1 11)
            (.step (.dropLo 4 128) <|
            .step (.xLo 129) <|
            .splitBase 3 331
              (.step (.dropLo 4 131) <|
              .step (.xLo 133) <|
              .missing 4 67)
              (.step (.primeLo 3 337) <|
              .step (.dropHi 4 132) <|
              .step (.xHi 129) <|
              .missing 4 13)))
          (.step (.primeLo 3 353) <|
          .step (.dropHi 4 130) <|
          .step (.xHi 129) <|
          .splitExp 1 4
            (.step (.grow 1 11) <|
            .missing 1 71)
            (.step (.dropLo 4 123) <|
            .step (.xLo 125) <|
            .splitBase 3 369
              (.step (.primeHi 3 367) <|
              .step (.dropLo 4 126) <|
              .step (.xLo 129) <|
              .missing 4 13)
              (.step (.primeLo 3 373) <|
              .step (.dropHi 4 127) <|
              .step (.xHi 125) <|
              .missing 4 7))))))

private def deficientFour5Part039Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,197,261,2,0⟩, ⟨true,113,185,1,1⟩], 1, deficientFour5Part038⟩]

theorem deficientFour5Part039 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,197,393,2,0⟩, ⟨true,89,185,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part039Tree deficientFour5Part039Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
