module

public import OddPerfect.DeficientPowerReplayGeneral.Part015

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart075Tree : Tree :=
  .step (.primeHi 3 2297) <|
  .splitBase 2 287
    (.step (.primeHi 2 283) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 3 1342) <|
      .step (.primeLo 3 1361) <|
      .splitExp 1 4
        (.missing 1 11)
        (.step (.dropLo 2 282) <|
        .step (.dropLo 3 2284) <|
        .step (.primeLo 2 283) <|
        .step (.primeLo 3 2287) <|
        .splitExp 0 8
          (.missing 0 13)
          (.reject))))
    (.step (.primeLo 2 293) <|
    .step (.dropHi 3 2020) <|
    .step (.primeHi 3 2017) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.splitExp 1 4
        (.missing 1 11)
        (.splitBase 3 1585
          (.use 0)
          (.step (.primeLo 3 1597) <|
          .step (.dropHi 2 304) <|
          .step (.primeHi 2 293) <|
          .step (.dropLo 3 1790) <|
          .step (.primeLo 3 1801) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 3 1947) <|
            .step (.primeLo 3 1949) <|
            .splitBase 3 1981
              (.step (.primeHi 3 1979) <|
              .splitExp 1 6
                (.step (.dropHi 3 1969) <|
                .step (.primeHi 3 1951) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.reject))
                (.reject))
              (.step (.primeLo 3 1987) <|
              .splitExp 1 6
                (.reject)
                (.step (.dropLo 3 1995) <|
                .step (.primeLo 3 1997) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 3 2015) <|
                  .step (.primeLo 3 2017) <|
                  .splitExp 0 12
                    (.splitExp 1 8
                      (.missing 1 19)
                      (.reject))
                    (.reject)))))))))

private def deficientFourPowerGeneralPart075Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,293,317,2,0⟩, ⟨false,1307,1585,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart074⟩]

theorem deficientFourPowerGeneralPart075 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,263,317,2,0⟩, ⟨false,1307,2299,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart075Tree deficientFourPowerGeneralPart075Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart076Tree : Tree :=
  .step (.primeLo 3 2851) <|
  .step (.dropHi 2 281) <|
  .splitBase 2 275
    (.step (.primeHi 2 271) <|
    .step (.dropLo 3 3562) <|
    .step (.primeLo 3 3571) <|
    .splitExp 0 8
      (.missing 0 13)
      (.reject))
    (.step (.primeLo 2 277) <|
    .step (.dropHi 3 3364) <|
    .step (.primeHi 3 3361) <|
    .splitExp 0 8
      (.missing 0 13)
      (.splitBase 3 3085
        (.step (.primeHi 3 3083) <|
        .splitBase 2 277
          (.reject)
          (.step (.primeLo 2 281) <|
          .step (.dropHi 3 2867) <|
          .step (.primeHi 3 2861) <|
          .splitExp 1 6
            (.reject)
            (.splitExp 0 10
              (.missing 0 23)
              (.step (.dropLo 3 2857) <|
              .splitExp 0 12
                (.splitExp 1 8
                  (.missing 1 19)
                  (.reject))
                (.reject)))))
        (.step (.primeLo 3 3089) <|
        .step (.dropHi 2 279) <|
        .step (.primeHi 2 277) <|
        .step (.dropLo 3 3167) <|
        .splitBase 3 3261
          (.step (.primeHi 3 3259) <|
          .splitExp 1 6
            (.step (.dropHi 3 3225) <|
            .step (.primeHi 3 3221) <|
            .splitExp 0 10
              (.missing 0 23)
              (.step (.dropLo 3 3218) <|
              .step (.primeLo 3 3221) <|
              .splitExp 0 12
                (.reject)
                (.reject)))
            (.reject))
          (.step (.primeLo 3 3271) <|
          .splitExp 1 6
            (.reject)
            (.step (.dropLo 3 3295) <|
            .step (.primeLo 3 3299) <|
            .splitExp 0 10
              (.missing 0 23)
              (.step (.dropLo 3 3350) <|
              .step (.primeLo 3 3359) <|
              .splitExp 0 12
                (.reject)
                (.splitExp 1 8
                  (.missing 1 19)
                  (.reject))))))))

theorem deficientFourPowerGeneralPart076 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,271,283,2,0⟩, ⟨false,2846,3709,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart076Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart077Tree : Tree :=
  .step (.primeHi 3 3709) <|
  .step (.dropLo 2 270) <|
  .step (.primeLo 2 271) <|
  .splitBase 3 2845
    (.step (.primeHi 3 2843) <|
    .step (.dropLo 2 276) <|
    .step (.primeLo 2 277) <|
    .splitBase 3 2547
      (.step (.primeHi 3 2543) <|
      .step (.dropLo 2 279) <|
      .step (.primeLo 2 281) <|
      .splitExp 0 8
        (.missing 0 13)
        (.reject))
      (.step (.primeLo 3 2549) <|
      .splitBase 2 279
        (.step (.primeHi 2 277) <|
        .step (.dropLo 3 2770) <|
        .step (.primeLo 3 2777) <|
        .splitExp 0 8
          (.missing 0 13)
          (.reject))
        (.step (.primeLo 2 281) <|
        .splitExp 0 8
          (.missing 0 13)
          (.splitBase 3 2687
            (.splitBase 2 281
              (.reject)
              (.step (.primeLo 2 283) <|
              .step (.dropHi 3 2673) <|
              .step (.primeHi 3 2671) <|
              .splitBase 3 2607
                (.step (.primeHi 3 2593) <|
                .splitExp 1 6
                  (.step (.dropHi 3 2585) <|
                  .step (.primeHi 3 2579) <|
                  .splitExp 0 10
                    (.missing 0 23)
                    (.reject))
                  (.reject))
                (.step (.primeLo 3 2609) <|
                .splitExp 1 6
                  (.reject)
                  (.step (.dropLo 3 2629) <|
                  .step (.primeLo 3 2633) <|
                  .splitExp 0 10
                    (.missing 0 23)
                    (.step (.dropLo 3 2665) <|
                    .step (.primeLo 3 2671) <|
                    .splitExp 0 12
                      (.reject)
                      (.splitExp 1 8
                        (.missing 1 19)
                        (.reject)))))))
            (.step (.primeLo 3 2689) <|
            .step (.dropHi 2 282) <|
            .step (.primeHi 2 281) <|
            .step (.dropLo 3 2722) <|
            .step (.primeLo 3 2729) <|
            .splitExp 1 6
              (.step (.dropHi 3 2765) <|
              .step (.primeHi 3 2753) <|
              .splitExp 0 10
                (.missing 0 23)
                (.reject))
              (.step (.dropLo 3 2816) <|
              .step (.primeLo 3 2819) <|
              .splitExp 0 10
                (.missing 0 23)
                (.reject)))))))
    (.use 0)

private def deficientFourPowerGeneralPart077Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,271,283,2,0⟩, ⟨false,2846,3709,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart076⟩]

theorem deficientFourPowerGeneralPart077 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,263,283,2,0⟩, ⟨false,2309,3717,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart077Tree deficientFourPowerGeneralPart077Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart078Tree : Tree :=
  .step (.primeLo 3 4363) <|
  .splitExp 0 8
    (.missing 0 13)
    (.splitBase 3 4775
      (.step (.primeHi 3 4759) <|
      .splitBase 2 269
        (.reject)
        (.step (.primeLo 2 271) <|
        .step (.dropHi 3 4608) <|
        .step (.primeHi 3 4603) <|
        .splitExp 1 6
          (.reject)
          (.step (.dropLo 3 4479) <|
          .step (.primeLo 3 4481) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 3 4582) <|
            .step (.primeLo 3 4583) <|
            .splitBase 3 4591
              (.splitExp 0 12
                (.splitExp 1 8
                  (.missing 1 19)
                  (.reject))
                (.reject))
              (.step (.primeLo 3 4597) <|
              .splitExp 0 12
                (.reject)
                (.splitExp 1 8
                  (.missing 1 19)
                  (.reject)))))))
      (.step (.primeLo 3 4783) <|
      .step (.dropHi 2 270) <|
      .step (.primeHi 2 269) <|
      .step (.dropLo 3 4807) <|
      .step (.primeLo 3 4813) <|
      .splitBase 3 5031
        (.step (.primeHi 3 5023) <|
        .splitExp 1 6
          (.step (.dropHi 3 4943) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 3 4926) <|
            .step (.primeLo 3 4931) <|
            .splitExp 0 12
              (.reject)
              (.step (.dropLo 3 4939) <|
              .step (.primeLo 3 4943) <|
              .splitExp 0 14
                (.missing 0 11)
                (.splitExp 2 2
                  (.missing 2 13)
                  (.splitSpecial 5
                    (.missing 4 7)
                    (.reject))))))
          (.reject))
        (.step (.primeLo 3 5039) <|
        .splitExp 1 6
          (.reject)
          (.step (.dropLo 3 5109) <|
          .step (.primeLo 3 5113) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 3 5243) <|
            .step (.primeLo 3 5261) <|
            .splitExp 0 12
              (.reject)
              (.splitExp 1 8
                (.missing 1 19)
                (.step (.dropLo 3 5272) <|
                .step (.primeLo 3 5273) <|
                .splitExp 0 14
                  (.missing 0 11)
                  (.reject))))))))

theorem deficientFourPowerGeneralPart078 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,269,271,2,0⟩, ⟨false,4362,5273,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart078Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart079Tree : Tree :=
  .step (.primeLo 3 5381) <|
  .step (.dropHi 2 268) <|
  .step (.primeHi 2 263) <|
  .step (.dropLo 3 5950) <|
  .step (.primeLo 3 5953) <|
  .splitExp 0 8
    (.missing 0 13)
    (.step (.dropLo 3 8136) <|
    .step (.primeLo 3 8147) <|
    .splitBase 3 8793
      (.step (.primeHi 3 8783) <|
      .splitExp 1 6
        (.step (.dropHi 3 8535) <|
        .step (.primeHi 3 8527) <|
        .splitExp 0 10
          (.missing 0 23)
          (.step (.dropLo 3 8482) <|
          .step (.primeLo 3 8501) <|
          .splitExp 0 12
            (.reject)
            (.step (.dropLo 3 8522) <|
            .step (.primeLo 3 8527) <|
            .splitExp 0 14
              (.missing 0 11)
              (.reject))))
        (.reject))
      (.step (.primeLo 3 8803) <|
      .splitExp 1 6
        (.reject)
        (.step (.dropLo 3 9040) <|
        .step (.primeLo 3 9041) <|
        .splitExp 0 10
          (.missing 0 23)
          (.step (.dropLo 3 9469) <|
          .step (.primeLo 3 9473) <|
          .splitBase 3 9511
            (.splitExp 0 12
              (.splitExp 1 8
                (.missing 1 19)
                (.reject))
              (.reject))
            (.step (.primeLo 3 9521) <|
            .splitExp 0 12
              (.step (.dropHi 3 9524) <|
              .step (.primeHi 3 9521) <|
              .splitExp 1 8
                (.missing 1 19)
                (.splitExp 2 2
                  (.missing 2 7)
                  (.splitSpecial 5
                    (.missing 4 7)
                    (.reject))))
              (.splitExp 1 8
                (.missing 1 19)
                (.reject)))))))

theorem deficientFourPowerGeneralPart079 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,263,271,2,0⟩, ⟨false,5354,9551,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart079Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
