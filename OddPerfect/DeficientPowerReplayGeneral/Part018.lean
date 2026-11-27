module

public import OddPerfect.DeficientPowerReplayGeneral.Part017

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart085Tree : Tree :=
  .step (.primeHi 3 887) <|
  .splitExp 1 4
    (.missing 1 11)
    (.step (.dropLo 2 351) <|
    .step (.primeLo 2 353) <|
    .splitBase 2 367
      (.step (.dropLo 3 801) <|
      .step (.primeLo 3 809) <|
      .splitBase 3 845
        (.step (.primeHi 3 839) <|
        .step (.dropLo 2 359) <|
        .splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 2 365) <|
          .step (.dropLo 3 831) <|
          .step (.primeLo 2 367) <|
          .step (.primeLo 3 839) <|
          .splitExp 1 6
            (.reject)
            (.reject)))
        (.step (.primeLo 3 853) <|
        .step (.dropHi 2 365) <|
        .step (.primeHi 2 359) <|
        .splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 2 357) <|
          .step (.dropLo 3 875) <|
          .step (.primeLo 2 359) <|
          .step (.primeLo 3 877) <|
          .splitExp 1 6
            (.step (.dropHi 3 879) <|
            .step (.primeHi 3 877) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject))
            (.step (.dropLo 3 884) <|
            .step (.primeLo 3 887) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject)))))
      (.step (.primeLo 2 373) <|
      .step (.dropHi 3 813) <|
      .step (.primeHi 3 811) <|
      .splitBase 3 779
        (.step (.primeHi 3 773) <|
        .splitBase 2 377
          (.step (.primeHi 2 373) <|
          .reject)
          (.step (.primeLo 2 379) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 3 759) <|
            .step (.primeLo 3 761) <|
            .splitBase 2 379
              (.reject)
              (.step (.primeLo 2 383) <|
              .step (.dropHi 3 770) <|
              .step (.primeHi 3 769) <|
              .splitExp 1 6
                (.step (.dropHi 3 762) <|
                .step (.primeHi 3 761) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.reject))
                (.step (.dropLo 3 766) <|
                .step (.primeLo 3 769) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.reject))))))
        (.step (.primeLo 3 787) <|
        .step (.dropHi 2 378) <|
        .step (.primeHi 2 373) <|
        .splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 3 801) <|
          .step (.primeLo 3 809) <|
          .splitExp 1 6
            (.reject)
            (.splitExp 0 10
              (.missing 0 23)
              (.reject))))))

theorem deficientFourPowerGeneralPart085 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,331,383,2,0⟩, ⟨false,751,899,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart085Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart086Tree : Tree :=
  .step (.primeHi 3 997) <|
  .step (.dropLo 2 336) <|
  .step (.primeLo 2 337) <|
  .splitBase 2 343
    (.step (.primeHi 2 337) <|
    .step (.dropLo 3 994) <|
    .step (.primeLo 3 997) <|
    .splitExp 0 8
      (.missing 0 13)
      (.reject))
    (.step (.primeLo 2 347) <|
    .step (.dropHi 3 973) <|
    .step (.primeHi 3 971) <|
    .splitBase 3 937
      (.splitExp 0 8
        (.missing 0 13)
        (.step (.dropLo 2 349) <|
        .step (.dropLo 3 913) <|
        .step (.primeLo 3 919) <|
        .splitBase 2 349
          (.reject)
          (.step (.primeLo 2 353) <|
          .step (.dropHi 3 928) <|
          .step (.primeHi 3 919) <|
          .splitExp 1 6
            (.reject)
            (.reject))))
      (.step (.primeLo 3 941) <|
      .step (.dropHi 2 351) <|
      .step (.primeHi 2 349) <|
      .splitExp 0 8
        (.missing 0 13)
        (.splitBase 3 955
          (.step (.primeHi 3 953) <|
          .splitExp 1 6
            (.splitBase 2 347
              (.reject)
              (.step (.primeLo 2 349) <|
              .step (.dropHi 3 946) <|
              .step (.primeHi 3 941) <|
              .reject))
            (.step (.dropLo 2 348) <|
            .step (.dropLo 3 952) <|
            .step (.primeLo 2 349) <|
            .step (.primeLo 3 953) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject)))
          (.step (.primeLo 3 967) <|
          .step (.dropHi 2 347) <|
          .splitExp 1 6
            (.reject)
            (.splitExp 0 10
              (.missing 0 23)
              (.reject))))))

theorem deficientFourPowerGeneralPart086 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,331,353,2,0⟩, ⟨false,907,1003,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart086Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart087Tree : Tree :=
  .step (.primeLo 2 331) <|
  .step (.primeLo 3 337) <|
  .step (.dropHi 2 1061) <|
  .step (.dropHi 3 1126) <|
  .step (.primeHi 3 1123) <|
  .splitExp 0 4
    (.missing 0 11)
    (.splitBase 2 503
      (.step (.dropLo 3 370) <|
      .step (.primeLo 3 373) <|
      .splitBase 3 559
        (.use 0)
        (.step (.primeLo 3 563) <|
        .step (.dropHi 2 468) <|
        .step (.primeHi 2 467) <|
        .splitBase 3 749
          (.use 1)
          (.step (.primeLo 3 751) <|
          .step (.dropHi 2 387) <|
          .step (.primeHi 2 383) <|
          .splitExp 0 6
            (.step (.fix 0 1093 3) <|
            .reject)
            (.splitBase 3 899
              (.use 2)
              (.step (.primeLo 3 907) <|
              .step (.dropHi 2 356) <|
              .step (.primeHi 2 353) <|
              .splitExp 1 4
                (.missing 1 11)
                (.splitBase 3 1003
                  (.use 3)
                  (.step (.primeLo 3 1009) <|
                  .step (.dropHi 2 342) <|
                  .step (.primeHi 2 337) <|
                  .splitBase 3 1061
                    (.splitExp 0 8
                      (.missing 0 13)
                      (.step (.dropLo 2 335) <|
                      .step (.dropLo 3 1041) <|
                      .step (.primeLo 2 337) <|
                      .step (.primeLo 3 1049) <|
                      .splitExp 1 6
                        (.reject)
                        (.step (.dropLo 3 1054) <|
                        .step (.primeLo 3 1061) <|
                        .splitExp 0 10
                          (.missing 0 23)
                          (.splitExp 0 12
                            (.splitExp 1 8
                              (.missing 1 19)
                              (.reject))
                            (.reject)))))
                    (.step (.primeLo 3 1063) <|
                    .step (.dropHi 2 336) <|
                    .step (.primeHi 2 331) <|
                    .splitExp 0 8
                      (.missing 0 13)
                      (.step (.dropLo 3 1103) <|
                      .splitExp 1 6
                        (.step (.dropHi 3 1110) <|
                        .step (.primeHi 3 1109) <|
                        .splitExp 0 10
                          (.missing 0 23)
                          (.reject))
                        (.step (.dropLo 3 1118) <|
                        .step (.primeLo 3 1123) <|
                        .splitExp 0 10
                          (.missing 0 23)
                          (.reject)))))))))))
      (.step (.primeLo 2 509) <|
      .step (.primeLo 3 521) <|
      .reject))

private def deficientFourPowerGeneralPart087Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,331,503,2,0⟩, ⟨false,373,559,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart081⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,331,467,2,0⟩, ⟨false,563,749,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart084⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,331,383,2,0⟩, ⟨false,751,899,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart085⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,331,353,2,0⟩, ⟨false,907,1003,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart086⟩]

theorem deficientFourPowerGeneralPart087 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,326,0,2,0⟩, ⟨false,167,0,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart087Tree deficientFourPowerGeneralPart087Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart088Tree : Tree :=
  .splitBase 2 157
    (.step (.dropLo 3 103) <|
    .step (.dropLo 4 14) <|
    .step (.xLo 17) <|
    .splitExp 1 2
      (.missing 1 31)
      (.step (.dropLo 2 120) <|
      .step (.dropLo 3 508) <|
      .step (.primeLo 2 127) <|
      .step (.primeLo 3 509) <|
      .splitExp 0 4
        (.missing 0 11)
        (.reject)))
    (.step (.primeLo 2 163) <|
    .step (.primeLo 3 167) <|
    .splitExp 1 2
      (.missing 1 31)
      (.step (.dropLo 4 15) <|
      .step (.xLo 17) <|
      .splitBase 2 325
        (.step (.primeHi 2 317) <|
        .step (.dropLo 3 192) <|
        .step (.primeLo 3 193) <|
        .splitExp 0 4
          (.missing 0 11)
          (.step (.dropLo 2 213) <|
          .step (.dropLo 3 653) <|
          .step (.primeLo 2 223) <|
          .splitBase 3 1305
            (.step (.primeHi 3 1303) <|
            .step (.dropLo 2 255) <|
            .step (.primeLo 2 257) <|
            .splitBase 3 869
              (.step (.primeHi 3 863) <|
              .step (.dropLo 2 283) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.reject))
              (.step (.primeLo 3 877) <|
              .splitBase 2 283
                (.splitExp 0 6
                  (.step (.fix 0 1093 3) <|
                  .step (.dropLo 2 265) <|
                  .step (.primeLo 2 269) <|
                  .splitExp 1 4
                    (.missing 1 11)
                    (.reject))
                  (.reject))
                (.step (.primeLo 2 293) <|
                .splitExp 0 6
                  (.step (.fix 0 1093 3) <|
                  .reject)
                  (.step (.dropLo 3 889) <|
                  .step (.primeLo 3 907) <|
                  .splitExp 1 4
                    (.missing 1 11)
                    (.step (.dropLo 2 312) <|
                    .step (.dropLo 3 1222) <|
                    .step (.primeLo 2 313) <|
                    .step (.primeLo 3 1223) <|
                    .splitExp 0 8
                      (.missing 0 13)
                      (.step (.dropLo 2 316) <|
                      .step (.dropLo 3 1294) <|
                      .step (.primeLo 2 317) <|
                      .step (.primeLo 3 1297) <|
                      .splitExp 1 6
                        (.splitExp 0 10
                          (.missing 0 23)
                          (.step (.dropLo 3 1302) <|
                          .step (.primeLo 3 1303) <|
                          .splitExp 0 12
                            (.reject)
                            (.reject)))
                        (.reject)))))))
            (.use 0)))
        (.use 1)))

private def deficientFourPowerGeneralPart088Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,223,317,2,0⟩, ⟨false,1306,0,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart080⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,326,0,2,0⟩, ⟨false,167,0,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart087⟩]

theorem deficientFourPowerGeneralPart088 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,79,0,2,0⟩, ⟨false,83,0,2,0⟩, ⟨true,13,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart088Tree deficientFourPowerGeneralPart088Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart089Tree : Tree :=
  .splitBase 2 33
    (.step (.primeHi 2 31) <|
    .step (.dropLo 4 13) <|
    .splitBase 3 37
      (.use 0)
      (.step (.primeLo 3 41) <|
      .splitExp 0 2
        (.step (.grow 0 13) <|
        .step (.dropHi 4 59) <|
        .step (.xHi 13) <|
        .missing 4 7)
        (.step (.dropLo 4 23) <|
        .step (.xLo 25) <|
        .splitBase 2 21
          (.use 1)
          (.step (.primeLo 2 23) <|
          .splitBase 3 81
            (.step (.primeHi 3 79) <|
            .step (.dropLo 4 32) <|
            .step (.xLo 33) <|
            .splitBase 3 53
              (.step (.dropLo 4 40) <|
              .step (.xLo 41) <|
              .splitBase 2 25
                (.use 2)
                (.step (.primeLo 2 29) <|
                .step (.dropHi 4 210) <|
                .step (.xHi 209) <|
                .splitExp 1 2
                  (.step (.dropHi 4 78) <|
                  .step (.xHi 77) <|
                  .step (.fix 1 31 2) <|
                  .step (.dropHi 4 66) <|
                  .step (.xHi 65) <|
                  .splitBase 3 45
                    (.step (.primeHi 3 43) <|
                    .step (.dropLo 4 49) <|
                    .splitExp 0 4
                      (.missing 0 11)
                      (.step (.dropLo 4 60) <|
                      .step (.xLo 61) <|
                      .splitBase 3 41
                        (.step (.dropLo 4 64) <|
                        .step (.xLo 65) <|
                        .missing 4 11)
                        (.step (.primeLo 3 43) <|
                        .step (.dropHi 4 62) <|
                        .step (.xHi 61) <|
                        .splitExp 0 6
                          (.missing 0 1093)
                          (.reject))))
                    (.step (.primeLo 3 47) <|
                    .step (.dropHi 4 55) <|
                    .step (.xHi 53) <|
                    .splitExp 0 4
                      (.missing 0 11)
                      (.step (.dropLo 4 47) <|
                      .step (.xLo 49) <|
                      .step (.dropHi 3 52) <|
                      .step (.primeHi 3 47) <|
                      .reject)))
                  (.use 3)))
              (.use 4))
            (.use 5)))))
    (.step (.primeLo 2 37) <|
    .step (.primeLo 3 41) <|
    .step (.dropHi 4 80) <|
    .step (.xHi 77) <|
    .splitExp 0 2
      (.step (.grow 0 13) <|
      .step (.dropHi 4 20) <|
      .step (.xLo 13) <|
      .step (.xHi 13) <|
      .missing 4 7)
      (.step (.dropLo 4 13) <|
      .splitBase 2 73
        (.use 6)
        (.step (.primeLo 2 79) <|
        .step (.primeLo 3 83) <|
        .step (.dropHi 4 25) <|
        .splitBase 4 17
          (.use 7)
          (.step (.xLo 21) <|
          .step (.dropHi 2 276) <|
          .step (.dropHi 3 332) <|
          .step (.primeHi 3 331) <|
          .step (.primeHi 2 271) <|
          .splitExp 1 2
            (.missing 1 31)
            (.splitBase 3 131
              (.step (.primeHi 2 127) <|
              .splitExp 0 4
                (.missing 0 11)
                (.splitBase 2 97
                  (.splitBase 3 101
                    (.step (.dropLo 4 22) <|
                    .step (.xLo 25) <|
                    .missing 4 13)
                    (.step (.primeLo 3 103) <|
                    .step (.dropHi 4 24) <|
                    .step (.xHi 21) <|
                    .missing 4 11))
                  (.step (.primeLo 2 101) <|
                  .step (.primeLo 3 103) <|
                  .step (.dropHi 4 22) <|
                  .step (.xHi 21) <|
                  .missing 4 11)))
              (.step (.primeLo 3 137) <|
              .step (.dropHi 2 119) <|
              .step (.dropHi 4 22) <|
              .step (.primeHi 2 113) <|
              .step (.xHi 21) <|
              .missing 4 11))))))

private def deficientFourPowerGeneralPart089Refs : List Known := [
  ⟨#v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,31,2,0⟩, ⟨false,19,37,2,0⟩, ⟨true,13,0,5,0⟩], 1, deficientFourPowerGeneralPart014⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,21,2,0⟩, ⟨false,41,0,2,0⟩, ⟨true,25,0,5,0⟩], 1, deficientFourPowerGeneralPart056⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,25,2,0⟩, ⟨false,41,53,2,0⟩, ⟨true,41,0,5,0⟩], 1, deficientFourPowerGeneralPart057⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,29,31,2,0⟩, ⟨false,41,53,2,0⟩, ⟨true,41,209,5,0⟩], 1, deficientFourPowerGeneralPart058⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,31,2,0⟩, ⟨false,54,79,2,0⟩, ⟨true,33,0,5,0⟩], 1, deficientFourPowerGeneralPart060⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,31,2,0⟩, ⟨false,82,0,2,0⟩, ⟨true,25,0,5,0⟩], 1, deficientFourPowerGeneralPart065⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,37,73,2,0⟩, ⟨false,41,0,2,0⟩, ⟨true,13,77,5,0⟩], 1, deficientFourPowerGeneralPart070⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,79,0,2,0⟩, ⟨false,83,0,2,0⟩, ⟨true,13,17,5,0⟩], 1, deficientFourPowerGeneralPart088⟩]

theorem deficientFourPowerGeneralPart089 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,9,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart089Tree deficientFourPowerGeneralPart089Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
