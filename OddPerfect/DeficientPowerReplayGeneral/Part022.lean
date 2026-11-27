module

public import OddPerfect.DeficientPowerReplayGeneral.Part021

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart105Tree : Tree :=
  .step (.primeHi 3 3229) <|
  .splitBase 2 273
    (.step (.primeHi 2 271) <|
    .step (.dropLo 3 1868) <|
    .step (.primeLo 3 1871) <|
    .splitExp 1 2
      (.missing 1 307)
      (.step (.dropLo 2 269) <|
      .step (.dropLo 3 3007) <|
      .step (.primeLo 3 3011) <|
      .splitSpecial 5
        (.missing 4 7)
        (.reject)))
    (.step (.primeLo 2 277) <|
    .splitBase 3 2189
      (.step (.primeHi 3 2179) <|
      .splitExp 1 2
        (.missing 1 307)
        (.step (.dropLo 2 280) <|
        .step (.primeLo 2 281) <|
        .splitBase 2 285
          (.step (.primeHi 2 283) <|
          .step (.dropLo 3 2042) <|
          .step (.primeLo 3 2053) <|
          .splitSpecial 5
            (.missing 4 7)
            (.reject))
          (.step (.primeLo 2 293) <|
          .step (.dropHi 3 2020) <|
          .step (.primeHi 3 2017) <|
          .splitBase 3 1819
            (.step (.primeHi 3 1811) <|
            .splitSpecial 5
              (.missing 4 7)
              (.reject))
            (.step (.primeLo 3 1823) <|
            .splitSpecial 5
              (.missing 4 7)
              (.step (.dropLo 3 1829) <|
              .step (.primeLo 3 1831) <|
              .splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 3 1994) <|
                .step (.primeLo 3 1997) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 3 2014) <|
                  .step (.primeLo 3 2017) <|
                  .splitExp 1 4
                    (.splitExp 0 12
                      (.reject)
                      (.splitSpecial 9
                        (.missing 4 11)
                        (.reject)))
                    (.reject))))))))
      (.use 0))

private def deficientFourPowerGeneralPart105Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,17,17,2,0⟩, ⟨false,277,293,2,0⟩, ⟨false,2190,3229,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart104⟩]

theorem deficientFourPowerGeneralPart105 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,293,2,0⟩, ⟨false,1657,3231,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart105Tree deficientFourPowerGeneralPart105Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart106Tree : Tree :=
  .step (.primeLo 3 4027) <|
  .step (.dropHi 2 273) <|
  .step (.primeHi 2 271) <|
  .splitSpecial 5
    (.missing 4 7)
    (.splitExp 0 8
      (.missing 0 13)
      (.step (.dropLo 3 4473) <|
      .step (.primeLo 3 4481) <|
      .splitBase 3 4843
        (.step (.primeHi 3 4831) <|
        .splitBase 2 269
          (.reject)
          (.step (.primeLo 2 271) <|
          .step (.dropHi 3 4608) <|
          .step (.primeHi 3 4603) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 3 4576) <|
            .step (.primeLo 3 4583) <|
            .splitBase 3 4591
              (.splitExp 1 4
                (.splitExp 0 12
                  (.reject)
                  (.step (.dropLo 3 4588) <|
                  .step (.primeLo 3 4591) <|
                  .splitSpecial 9
                    (.missing 4 11)
                    (.splitExp 0 14
                      (.missing 0 11)
                      (.reject))))
                (.reject))
              (.step (.primeLo 3 4597) <|
              .splitExp 1 4
                (.reject)
                (.splitExp 0 12
                  (.reject)
                  (.reject))))))
        (.step (.primeLo 3 4861) <|
        .step (.dropHi 2 270) <|
        .step (.primeHi 2 269) <|
        .step (.dropLo 3 5102) <|
        .step (.primeLo 3 5107) <|
        .splitExp 0 10
          (.missing 0 23)
          (.step (.dropLo 3 5236) <|
          .step (.primeLo 3 5237) <|
          .splitBase 3 5253
            (.step (.primeHi 3 5237) <|
            .splitExp 1 4
              (.splitExp 0 12
                (.splitSpecial 9
                  (.missing 4 11)
                  (.reject))
                (.reject))
              (.reject))
            (.step (.primeLo 3 5261) <|
            .splitExp 1 4
              (.reject)
              (.splitExp 0 12
                (.reject)
                (.step (.dropLo 3 5271) <|
                .step (.primeLo 3 5273) <|
                .splitSpecial 9
                  (.missing 4 11)
                  (.reject))))))))

theorem deficientFourPowerGeneralPart106 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨false,4022,5273,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart106Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart107Tree : Tree :=
  .step (.primeHi 3 11321) <|
  .splitBase 2 259
    (.step (.primeHi 2 257) <|
    .step (.dropLo 3 7643) <|
    .splitSpecial 5
      (.missing 4 7)
      (.reject))
    (.step (.primeLo 2 263) <|
    .step (.dropHi 3 9581) <|
    .step (.primeHi 3 9551) <|
    .splitSpecial 5
      (.missing 4 7)
      (.step (.dropLo 3 6409) <|
      .step (.primeLo 3 6421) <|
      .splitExp 0 8
        (.missing 0 13)
        (.step (.dropLo 3 9019) <|
        .step (.primeLo 3 9029) <|
        .splitExp 0 10
          (.missing 0 23)
          (.step (.dropLo 3 9446) <|
          .step (.primeLo 3 9461) <|
          .splitBase 3 9505
            (.step (.primeHi 3 9497) <|
            .splitExp 1 4
              (.splitExp 0 12
                (.step (.dropHi 3 9461) <|
                .splitSpecial 9
                  (.missing 4 11)
                  (.splitExp 2 2
                    (.missing 2 7)
                    (.reject)))
                (.step (.dropLo 3 9496) <|
                .step (.primeLo 3 9497) <|
                .splitSpecial 9
                  (.missing 4 11)
                  (.reject)))
              (.reject))
            (.step (.primeLo 3 9511) <|
            .splitExp 1 4
              (.step (.dropHi 3 9517) <|
              .step (.primeHi 3 9511) <|
              .splitExp 0 12
                (.reject)
                (.splitSpecial 9
                  (.missing 4 11)
                  (.splitExp 0 14
                    (.missing 0 11)
                    (.reject))))
              (.splitExp 0 12
                (.step (.dropHi 3 9524) <|
                .step (.primeHi 3 9521) <|
                .splitSpecial 9
                  (.missing 4 11)
                  (.step (.dropLo 3 9519) <|
                  .step (.primeLo 3 9521) <|
                  .splitExp 2 2
                    (.missing 2 7)
                    (.reject)))
                (.reject)))))))

theorem deficientFourPowerGeneralPart107 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,263,2,0⟩, ⟨false,6197,11323,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart107Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart108Tree : Tree :=
  .step (.primeLo 3 62477) <|
  .splitExp 1 4
    (.step (.dropHi 3 62644) <|
    .step (.primeHi 3 62639) <|
    .splitExp 0 12
      (.reject)
      (.splitSpecial 9
        (.missing 4 11)
        (.splitExp 0 14
          (.missing 0 11)
          (.splitExp 2 2
            (.missing 2 61)
            (.step (.dropLo 3 62613) <|
            .step (.primeLo 3 62617) <|
            .splitExp 0 16
              (.missing 0 1871)
              (.reject))))))
    (.splitExp 0 12
      (.step (.dropHi 3 62948) <|
      .step (.primeHi 3 62939) <|
      .splitSpecial 9
        (.missing 4 11)
        (.step (.dropLo 3 62705) <|
        .step (.primeLo 3 62723) <|
        .splitExp 2 2
          (.missing 2 61)
          (.step (.dropLo 3 62938) <|
          .step (.primeLo 3 62939) <|
          .splitExp 1 6
            (.reject)
            (.reject))))
      (.step (.dropLo 3 64548) <|
      .step (.primeLo 3 64553) <|
      .splitBase 3 65033
        (.splitSpecial 9
          (.missing 4 11)
          (.step (.dropLo 3 64977) <|
          .step (.primeLo 3 64997) <|
          .splitExp 0 14
            (.missing 0 11)
            (.reject)))
        (.step (.primeLo 3 65053) <|
        .splitSpecial 9
          (.missing 4 11)
          (.splitBase 3 65285
            (.step (.primeHi 3 65269) <|
            .splitExp 0 14
              (.missing 0 11)
              (.step (.dropLo 3 65239) <|
              .splitExp 2 2
                (.missing 2 61)
                (.reject)))
            (.step (.primeLo 3 65287) <|
            .splitExp 0 14
              (.missing 0 11)
              (.splitExp 2 2
                (.missing 2 61)
                (.step (.dropLo 3 65491) <|
                .step (.primeLo 3 65497) <|
                .splitExp 0 16
                  (.missing 0 1871)
                  (.reject))))))))

theorem deficientFourPowerGeneralPart108 : Closed (#v[⟨false,3,3,12,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62474,65521,2,0⟩, ⟨true,5,5,9,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart108Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart109Tree : Tree :=
  .step (.primeLo 3 6197) <|
  .step (.dropHi 2 266) <|
  .step (.primeHi 2 263) <|
  .splitExp 1 2
    (.missing 1 307)
    (.splitBase 3 11323
      (.use 0)
      (.step (.primeLo 3 11329) <|
      .step (.dropHi 2 261) <|
      .step (.primeHi 2 257) <|
      .splitSpecial 5
        (.missing 4 7)
        (.step (.dropLo 3 14941) <|
        .step (.primeLo 3 14947) <|
        .splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 3 45936) <|
          .step (.primeLo 3 45943) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 3 59695) <|
            .step (.primeLo 3 59699) <|
            .splitBase 3 62473
              (.splitExp 1 4
                (.splitExp 0 12
                  (.step (.dropHi 3 60276) <|
                  .step (.primeHi 3 60271) <|
                  .splitBase 3 59983
                    (.step (.primeHi 3 59981) <|
                    .splitSpecial 9
                      (.missing 4 11)
                      (.reject))
                    (.step (.primeLo 3 59999) <|
                    .splitSpecial 9
                      (.missing 4 11)
                      (.step (.dropLo 3 60062) <|
                      .step (.primeLo 3 60077) <|
                      .splitExp 2 2
                        (.missing 2 61)
                        (.reject))))
                  (.step (.dropLo 3 61750) <|
                  .step (.primeLo 3 61751) <|
                  .splitBase 3 62109
                    (.step (.primeHi 3 62099) <|
                    .splitSpecial 9
                      (.missing 4 11)
                      (.reject))
                    (.step (.primeLo 3 62119) <|
                    .splitSpecial 9
                      (.missing 4 11)
                      (.step (.dropLo 3 62143) <|
                      .splitExp 0 14
                        (.missing 0 11)
                        (.step (.dropLo 3 62383) <|
                        .splitExp 2 2
                          (.missing 2 61)
                          (.reject))))))
                (.step (.dropLo 3 62306) <|
                .step (.primeLo 3 62311) <|
                .splitExp 0 12
                  (.splitSpecial 9
                    (.missing 4 11)
                    (.reject))
                  (.reject)))
              (.use 1))))))

private def deficientFourPowerGeneralPart109Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,263,2,0⟩, ⟨false,6197,11323,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart107⟩,
  ⟨#v[⟨false,3,3,12,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62474,65521,2,0⟩, ⟨true,5,5,9,0⟩], 1, deficientFourPowerGeneralPart108⟩]

theorem deficientFourPowerGeneralPart109 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,277,2,0⟩, ⟨false,6194,65521,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart109Tree deficientFourPowerGeneralPart109Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
