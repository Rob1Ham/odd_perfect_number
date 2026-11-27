module

public import OddPerfect.DeficientTree

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour11Part000Tree : Tree :=
  .step (.primeHi 2 83) <|
  .step (.dropLo 3 356) <|
  .step (.primeLo 3 359) <|
  .splitExp 0 4
    (.splitBase 2 73
      (.step (.dropLo 3 881) <|
      .splitBase 2 69
        (.step (.primeHi 2 67) <|
        .reject)
        (.step (.primeLo 2 71) <|
        .splitBase 3 1761
          (.step (.primeHi 3 1759) <|
          .splitExp 1 2
            (.missing 1 7)
            (.reject))
          (.step (.primeLo 3 1777) <|
          .splitExp 1 2
            (.missing 1 7)
            (.step (.dropLo 3 2567) <|
            .step (.primeLo 3 2579) <|
            .splitBase 2 71
              (.reject)
              (.step (.primeLo 2 73) <|
              .step (.dropHi 3 2627) <|
              .step (.primeHi 3 2621) <|
              .splitExp 1 4
                (.step (.grow 1 5) <|
                .step (.dropHi 3 2584) <|
                .step (.primeHi 3 2579) <|
                .splitExp 2 2
                  (.missing 2 1801)
                  (.reject))
                (.step (.dropLo 3 2609) <|
                .splitExp 2 2
                  (.missing 2 1801)
                  (.reject)))))))
      (.step (.primeLo 2 79) <|
      .step (.dropHi 3 697) <|
      .step (.primeHi 3 691) <|
      .splitBase 3 471
        (.step (.primeHi 3 467) <|
        .splitExp 1 2
          (.missing 1 7)
          (.reject))
        (.step (.primeLo 3 479) <|
        .splitExp 1 2
          (.missing 1 7)
          (.step (.dropLo 3 485) <|
          .step (.primeLo 3 487) <|
          .splitBase 2 79
            (.reject)
            (.step (.primeLo 2 83) <|
            .step (.dropHi 3 487) <|
            .splitExp 1 4
              (.step (.grow 1 5) <|
              .reject)
              (.reject))))))
    (.reject)

theorem deficientFour11Part000 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,67,87,2,0⟩, ⟨false,139,0,2,0⟩, ⟨true,5,5,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour11Part000Tree [] _ _ (by decide +kernel)

private def deficientFour11Part001Tree : Tree :=
  .step (.primeLo 3 4441) <|
  .step (.dropHi 2 102) <|
  .step (.primeHi 2 101) <|
  .step (.dropLo 3 6329) <|
  .splitExp 0 8
    (.missing 0 13)
    (.step (.dropLo 3 8863) <|
    .splitBase 3 9385
      (.step (.primeHi 3 9377) <|
      .splitExp 1 4
        (.step (.grow 1 5) <|
        .splitExp 0 10
          (.missing 0 23)
          (.step (.dropLo 3 9275) <|
          .step (.primeLo 3 9277) <|
          .splitExp 2 2
            (.step (.dropHi 3 9330) <|
            .step (.primeHi 3 9323) <|
            .splitExp 0 12
              (.reject)
              (.reject))
            (.step (.dropLo 3 9360) <|
            .step (.primeLo 3 9371) <|
            .splitExp 0 12
              (.reject)
              (.reject))))
        (.step (.dropLo 3 9375) <|
        .step (.primeLo 3 9377) <|
        .splitExp 0 10
          (.missing 0 23)
          (.reject)))
      (.step (.primeLo 3 9391) <|
      .splitExp 1 4
        (.step (.grow 1 5) <|
        .step (.dropHi 3 9415) <|
        .step (.primeHi 3 9413) <|
        .splitExp 0 10
          (.missing 0 23)
          (.splitExp 2 2
            (.reject)
            (.splitExp 0 12
              (.reject)
              (.step (.dropLo 3 9409) <|
              .step (.primeLo 3 9413) <|
              .splitExp 0 14
                (.missing 0 13)
                (.reject)))))
        (.splitExp 0 10
          (.missing 0 23)
          (.step (.dropLo 3 9837) <|
          .step (.primeLo 3 9839) <|
          .splitBase 3 9905
            (.step (.primeHi 3 9901) <|
            .splitExp 2 2
              (.splitExp 0 12
                (.step (.dropHi 3 9842) <|
                .step (.primeHi 3 9839) <|
                .splitExp 1 6
                  (.missing 1 43)
                  (.reject))
                (.step (.dropLo 3 9892) <|
                .step (.primeLo 3 9901) <|
                .splitExp 0 14
                  (.missing 0 13)
                  (.splitExp 1 6
                    (.missing 1 43)
                    (.reject))))
              (.reject))
            (.step (.primeLo 3 9907) <|
            .splitExp 2 2
              (.reject)
              (.step (.dropLo 3 9932) <|
              .step (.primeLo 3 9941) <|
              .splitExp 0 12
                (.reject)
                (.reject)))))))

theorem deficientFour11Part001 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,11,11,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,4424,9973,2,0⟩, ⟨true,5,5,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour11Part001Tree [] _ _ (by decide +kernel)

private def deficientFour11Part002Tree : Tree :=
  .step (.primeLo 3 2729) <|
  .splitExp 0 6
    (.missing 0 1093)
    (.step (.dropLo 2 99) <|
    .step (.dropLo 3 2840) <|
    .step (.primeLo 2 101) <|
    .step (.primeLo 3 2843) <|
    .step (.dropHi 3 10000) <|
    .step (.primeHi 3 9973) <|
    .splitBase 3 4423
      (.splitBase 2 101
        (.reject)
        (.step (.primeLo 2 103) <|
        .step (.dropHi 3 3400) <|
        .step (.primeHi 3 3391) <|
        .splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 3 3258) <|
          .step (.primeLo 3 3259) <|
          .splitBase 3 3323
            (.splitExp 1 4
              (.step (.grow 1 5) <|
              .splitExp 0 10
                (.missing 0 23)
                (.step (.dropLo 3 3312) <|
                .step (.primeLo 3 3313) <|
                .splitExp 2 2
                  (.step (.dropHi 3 3319) <|
                  .splitExp 0 12
                    (.reject)
                    (.step (.dropLo 3 3318) <|
                    .step (.primeLo 3 3319) <|
                    .splitExp 0 14
                      (.missing 0 13)
                      (.reject)))
                  (.step (.dropLo 3 3322) <|
                  .step (.primeLo 3 3323) <|
                  .splitExp 0 12
                    (.reject)
                    (.reject))))
              (.reject))
            (.step (.primeLo 3 3329) <|
            .splitExp 1 4
              (.step (.grow 1 5) <|
              .step (.dropHi 3 3329) <|
              .splitExp 0 10
                (.missing 0 23)
                (.splitExp 2 2
                  (.reject)
                  (.splitExp 0 12
                    (.reject)
                    (.splitExp 0 14
                      (.missing 0 13)
                      (.reject)))))
              (.splitExp 0 10
                (.missing 0 23)
                (.step (.dropLo 3 3381) <|
                .step (.primeLo 3 3389) <|
                .splitExp 2 2
                  (.step (.dropHi 3 3389) <|
                  .splitExp 0 12
                    (.reject)
                    (.splitExp 0 14
                      (.missing 0 13)
                      (.splitExp 1 6
                        (.missing 1 43)
                        (.reject))))
                  (.reject)))))))
      (.use 0))

private def deficientFour11Part002Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,11,11,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,4424,9973,2,0⟩, ⟨true,5,5,1,1⟩], 1, deficientFour11Part001⟩]

theorem deficientFour11Part002 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,2722,0,2,0⟩, ⟨true,5,5,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour11Part002Tree deficientFour11Part002Refs _ _ (by decide +kernel)

private def deficientFour11Part003Tree : Tree :=
  .step (.primeHi 3 467) <|
  .step (.dropLo 2 110) <|
  .step (.primeLo 2 113) <|
  .splitBase 3 349
    (.step (.dropLo 2 119) <|
    .step (.primeLo 2 127) <|
    .splitExp 1 2
      (.missing 1 7)
      (.reject))
    (.step (.primeLo 3 353) <|
    .splitBase 2 121
      (.step (.primeHi 2 113) <|
      .step (.dropLo 3 422) <|
      .step (.primeLo 3 431) <|
      .splitExp 1 2
        (.missing 1 7)
        (.reject))
      (.step (.primeLo 2 127) <|
      .step (.dropHi 3 466) <|
      .step (.primeHi 3 463) <|
      .splitExp 1 2
        (.missing 1 7)
        (.splitBase 3 399
          (.step (.primeHi 3 397) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.reject))
          (.step (.primeLo 3 401) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 3 409) <|
            .splitBase 3 433
              (.step (.dropLo 2 128) <|
              .step (.primeLo 2 131) <|
              .step (.dropHi 3 419) <|
              .splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 3 417) <|
                .step (.primeLo 3 419) <|
                .splitExp 1 4
                  (.step (.grow 1 5) <|
                  .reject)
                  (.splitExp 0 10
                    (.missing 0 23)
                    (.reject))))
              (.step (.primeLo 3 439) <|
              .step (.dropHi 2 129) <|
              .step (.primeHi 2 127) <|
              .step (.dropLo 3 454) <|
              .step (.primeLo 3 457) <|
              .splitExp 0 8
                (.missing 0 13)
                (.reject)))))))

theorem deficientFour11Part003 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,11,11,2,0⟩, ⟨false,107,131,2,0⟩, ⟨false,281,473,2,0⟩, ⟨true,5,5,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour11Part003Tree [] _ _ (by decide +kernel)

private def deficientFour11Part004Tree : Tree :=
  .step (.primeLo 3 991) <|
  .step (.dropHi 2 111) <|
  .step (.primeHi 2 109) <|
  .splitExp 0 6
    (.step (.fix 0 1093 3) <|
    .reject)
    (.step (.dropLo 3 1122) <|
    .step (.primeLo 3 1123) <|
    .splitBase 3 1287
      (.step (.primeHi 3 1283) <|
      .splitBase 2 107
        (.reject)
        (.step (.primeLo 2 109) <|
        .step (.dropHi 3 1200) <|
        .step (.primeHi 3 1193) <|
        .splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 3 1182) <|
          .step (.primeLo 3 1187) <|
          .splitExp 1 4
            (.step (.grow 1 5) <|
            .step (.dropHi 3 1191) <|
            .step (.primeHi 3 1187) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject))
            (.step (.dropLo 3 1190) <|
            .step (.primeLo 3 1193) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject)))))
      (.step (.primeLo 3 1289) <|
      .step (.dropHi 2 108) <|
      .step (.primeHi 2 107) <|
      .step (.dropLo 3 1392) <|
      .step (.primeLo 3 1399) <|
      .splitExp 0 8
        (.missing 0 13)
        (.step (.dropLo 3 1485) <|
        .step (.primeLo 3 1487) <|
        .splitBase 3 1497
          (.step (.primeHi 3 1493) <|
          .splitExp 1 4
            (.step (.grow 1 5) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject))
            (.reject))
          (.step (.primeLo 3 1499) <|
          .splitExp 1 4
            (.step (.grow 1 5) <|
            .step (.dropHi 3 1500) <|
            .step (.primeHi 3 1499) <|
            .splitExp 0 10
              (.missing 0 23)
              (.splitExp 2 2
                (.missing 2 7)
                (.splitExp 0 12
                  (.reject)
                  (.reject))))
            (.splitExp 0 10
              (.missing 0 23)
              (.step (.dropLo 3 1510) <|
              .step (.primeLo 3 1511) <|
              .splitExp 2 2
                (.missing 2 7)
                (.reject)))))))

theorem deficientFour11Part004 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,988,1511,2,0⟩, ⟨true,5,5,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour11Part004Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
