module

public import OddPerfect.DeficientPowerReplayGeneral.Part016

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart080Tree : Tree :=
  .step (.primeLo 3 1307) <|
  .splitBase 2 261
    (.use 0)
    (.step (.primeLo 2 263) <|
    .step (.dropHi 3 9581) <|
    .step (.primeHi 3 9551) <|
    .splitBase 3 2299
      (.use 1)
      (.step (.primeLo 3 2309) <|
      .step (.dropHi 2 287) <|
      .step (.primeHi 2 283) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.splitExp 1 4
          (.missing 1 11)
          (.splitBase 3 3717
            (.use 2)
            (.step (.primeLo 3 3719) <|
            .step (.dropHi 2 274) <|
            .step (.primeHi 2 271) <|
            .splitBase 3 5353
              (.step (.primeHi 3 5351) <|
              .step (.dropLo 2 264) <|
              .step (.primeLo 2 269) <|
              .step (.dropHi 3 5277) <|
              .step (.primeHi 3 5273) <|
              .splitBase 3 4361
                (.step (.primeHi 3 4357) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.step (.dropLo 2 270) <|
                  .step (.dropLo 3 4245) <|
                  .step (.primeLo 2 271) <|
                  .step (.primeLo 3 4253) <|
                  .splitExp 1 6
                    (.step (.dropHi 3 4351) <|
                    .step (.primeHi 3 4349) <|
                    .splitExp 0 10
                      (.missing 0 23)
                      (.step (.dropLo 3 4337) <|
                      .splitExp 0 12
                        (.step (.dropHi 3 4339) <|
                        .splitBase 3 4337
                          (.reject)
                          (.step (.primeLo 3 4339) <|
                          .splitExp 2 2
                            (.reject)
                            (.splitSpecial 5
                              (.missing 4 7)
                              (.reject))))
                        (.step (.dropLo 3 4348) <|
                        .step (.primeLo 3 4349) <|
                        .splitExp 0 14
                          (.missing 0 11)
                          (.reject))))
                    (.reject)))
                (.use 3))
              (.use 4))))))

private def deficientFourPowerGeneralPart080Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,223,261,2,0⟩, ⟨false,1307,0,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart073⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,263,317,2,0⟩, ⟨false,1307,2299,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart075⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,263,283,2,0⟩, ⟨false,2309,3717,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart077⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,269,271,2,0⟩, ⟨false,4362,5273,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart078⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,263,271,2,0⟩, ⟨false,5354,9551,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart079⟩]

theorem deficientFourPowerGeneralPart080 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,223,317,2,0⟩, ⟨false,1306,0,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart080Tree deficientFourPowerGeneralPart080Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart081Tree : Tree :=
  .step (.primeHi 3 557) <|
  .step (.dropLo 2 345) <|
  .step (.primeLo 2 347) <|
  .splitBase 2 409
    (.step (.dropLo 3 446) <|
    .step (.primeLo 3 449) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 2 402) <|
      .step (.dropLo 3 544) <|
      .step (.primeLo 2 409) <|
      .step (.primeLo 3 547) <|
      .splitExp 1 4
        (.missing 1 11)
        (.reject)))
    (.step (.primeLo 2 419) <|
    .step (.primeLo 3 421) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 3 436) <|
      .step (.primeLo 3 439) <|
      .splitBase 3 491
        (.step (.primeHi 2 487) <|
        .step (.dropLo 2 445) <|
        .step (.dropLo 3 449) <|
        .step (.primeLo 2 449) <|
        .step (.primeLo 3 457) <|
        .splitExp 1 4
          (.missing 1 11)
          (.reject))
        (.step (.primeLo 3 499) <|
        .splitExp 1 4
          (.missing 1 11)
          (.step (.dropLo 2 459) <|
          .step (.dropLo 3 503) <|
          .step (.primeLo 2 461) <|
          .splitBase 3 527
            (.step (.primeHi 3 523) <|
            .step (.dropLo 2 485) <|
            .step (.primeLo 2 487) <|
            .splitBase 3 511
              (.step (.primeHi 3 509) <|
              .step (.dropLo 2 497) <|
              .step (.primeLo 2 499) <|
              .splitExp 0 8
                (.missing 0 13)
                (.reject))
              (.step (.primeLo 3 521) <|
              .step (.dropHi 2 502) <|
              .step (.primeHi 2 499) <|
              .splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 2 495) <|
                .step (.primeLo 2 499) <|
                .splitExp 1 6
                  (.step (.dropHi 3 521) <|
                  .splitExp 0 10
                    (.missing 0 23)
                    (.splitExp 0 12
                      (.reject)
                      (.reject)))
                  (.step (.dropLo 3 522) <|
                  .step (.primeLo 3 523) <|
                  .splitExp 0 10
                    (.missing 0 23)
                    (.reject)))))
            (.step (.primeLo 3 541) <|
            .step (.dropHi 2 485) <|
            .step (.primeHi 2 479) <|
            .splitBase 2 469
              (.step (.primeHi 2 467) <|
              .step (.dropLo 3 545) <|
              .step (.primeLo 3 547) <|
              .splitExp 0 8
                (.missing 0 13)
                (.reject))
              (.step (.primeLo 2 479) <|
              .step (.dropHi 3 548) <|
              .step (.primeHi 3 547) <|
              .splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 3 543) <|
                .step (.primeLo 3 547) <|
                .splitExp 1 6
                  (.reject)
                  (.splitExp 0 10
                    (.missing 0 23)
                    (.reject)))))))))

theorem deficientFourPowerGeneralPart081 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,331,503,2,0⟩, ⟨false,373,559,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart081Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart082Tree : Tree :=
  .step (.primeLo 2 449) <|
  .step (.dropHi 3 594) <|
  .step (.primeHi 3 593) <|
  .splitBase 3 577
    (.splitBase 2 457
      (.splitExp 0 8
        (.missing 0 13)
        (.step (.dropLo 2 455) <|
        .step (.dropLo 3 574) <|
        .step (.primeLo 2 457) <|
        .step (.primeLo 3 577) <|
        .splitExp 1 6
          (.reject)
          (.reject)))
      (.step (.primeLo 2 461) <|
      .step (.dropHi 3 574) <|
      .step (.primeHi 3 571) <|
      .splitExp 0 8
        (.missing 0 13)
        (.splitBase 2 463
          (.step (.dropLo 3 565) <|
          .step (.primeLo 3 569) <|
          .splitExp 1 6
            (.step (.dropHi 2 461) <|
            .step (.dropHi 3 570) <|
            .step (.primeHi 3 569) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject))
            (.splitBase 2 461
              (.reject)
              (.step (.primeLo 2 463) <|
              .splitExp 0 10
                (.missing 0 23)
                (.step (.dropLo 3 570) <|
                .step (.primeLo 3 571) <|
                .splitExp 0 12
                  (.splitExp 1 8
                    (.missing 1 19)
                    (.reject))
                  (.reject)))))
          (.step (.primeLo 2 467) <|
          .step (.dropHi 3 565) <|
          .step (.primeHi 3 563) <|
          .splitExp 1 6
            (.reject)
            (.reject)))))
    (.step (.primeLo 3 587) <|
    .step (.dropHi 2 453) <|
    .step (.primeHi 2 449) <|
    .splitExp 0 8
      (.missing 0 13)
      (.splitBase 3 589
        (.step (.primeHi 3 587) <|
        .reject)
        (.step (.primeLo 3 593) <|
        .splitExp 1 6
          (.reject)
          (.splitExp 0 10
            (.missing 0 23)
            (.reject)))))

theorem deficientFourPowerGeneralPart082 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,448,467,2,0⟩, ⟨false,563,619,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart082Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart083Tree : Tree :=
  .step (.primeLo 3 641) <|
  .step (.dropHi 2 425) <|
  .step (.primeHi 2 421) <|
  .splitExp 1 4
    (.missing 1 11)
    (.splitBase 3 687
      (.step (.primeHi 3 683) <|
      .step (.dropLo 2 398) <|
      .step (.primeLo 2 401) <|
      .splitBase 2 409
        (.step (.dropLo 3 654) <|
        .step (.primeLo 3 659) <|
        .splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 2 405) <|
          .step (.dropLo 3 674) <|
          .step (.primeLo 2 409) <|
          .step (.primeLo 3 677) <|
          .step (.dropHi 3 682) <|
          .step (.primeHi 3 677) <|
          .splitExp 1 6
            (.reject)
            (.reject)))
        (.step (.primeLo 2 419) <|
        .step (.dropHi 3 656) <|
        .step (.primeHi 3 653) <|
        .splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 3 643) <|
          .splitBase 3 647
            (.splitExp 1 6
              (.splitBase 2 419
                (.reject)
                (.step (.primeLo 2 421) <|
                .step (.dropHi 3 646) <|
                .step (.primeHi 3 643) <|
                .reject))
              (.reject))
            (.step (.primeLo 3 653) <|
            .step (.dropHi 2 420) <|
            .step (.primeHi 2 419) <|
            .splitExp 1 6
              (.reject)
              (.reject)))))
      (.step (.primeLo 3 691) <|
      .step (.dropHi 2 406) <|
      .step (.primeHi 2 401) <|
      .splitBase 3 715
        (.step (.primeHi 3 709) <|
        .step (.dropLo 2 390) <|
        .step (.primeLo 2 397) <|
        .splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 3 697) <|
          .step (.primeLo 3 701) <|
          .splitBase 2 397
            (.reject)
            (.step (.primeLo 2 401) <|
            .step (.dropHi 3 706) <|
            .step (.primeHi 3 701) <|
            .splitExp 1 6
              (.reject)
              (.reject))))
        (.step (.primeLo 3 719) <|
        .step (.dropHi 2 396) <|
        .step (.primeHi 2 389) <|
        .splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 3 736) <|
          .step (.primeLo 3 739) <|
          .splitExp 1 6
            (.step (.dropHi 3 739) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject))
            (.reject)))))

theorem deficientFourPowerGeneralPart083 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,389,467,2,0⟩, ⟨false,640,743,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart083Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart084Tree : Tree :=
  .step (.primeHi 3 743) <|
  .splitBase 2 387
    (.step (.primeHi 2 383) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 2 340) <|
      .step (.dropLo 3 599) <|
      .step (.primeLo 2 347) <|
      .splitExp 1 4
        (.missing 1 11)
        (.step (.dropLo 2 380) <|
        .step (.dropLo 3 734) <|
        .step (.primeLo 2 383) <|
        .step (.primeLo 3 739) <|
        .splitExp 0 8
          (.missing 0 13)
          (.reject))))
    (.step (.primeLo 2 389) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.splitBase 3 639
        (.step (.primeHi 3 631) <|
        .splitBase 2 423
          (.step (.primeHi 2 421) <|
          .splitExp 1 4
            (.missing 1 11)
            (.step (.dropLo 2 418) <|
            .step (.dropLo 3 625) <|
            .step (.primeLo 2 419) <|
            .step (.primeLo 3 631) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject)))
          (.step (.primeLo 2 431) <|
          .step (.dropHi 3 629) <|
          .step (.primeHi 3 619) <|
          .splitExp 1 4
            (.missing 1 11)
            (.splitBase 2 447
              (.step (.primeHi 2 443) <|
              .step (.dropLo 3 582) <|
              .step (.primeLo 3 587) <|
              .splitBase 3 601
                (.step (.dropLo 2 432) <|
                .step (.primeLo 2 433) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.step (.dropLo 2 441) <|
                  .step (.dropLo 3 598) <|
                  .step (.primeLo 2 443) <|
                  .step (.primeLo 3 599) <|
                  .splitExp 1 6
                    (.step (.dropHi 3 600) <|
                    .step (.primeHi 3 599) <|
                    .splitExp 0 10
                      (.missing 0 23)
                      (.reject))
                    (.reject)))
                (.step (.primeLo 3 607) <|
                .step (.dropHi 2 441) <|
                .step (.primeHi 2 439) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.step (.dropLo 2 432) <|
                  .step (.primeLo 2 433) <|
                  .splitBase 3 611
                    (.step (.primeHi 3 607) <|
                    .step (.dropLo 2 438) <|
                    .step (.primeLo 2 439) <|
                    .splitExp 1 6
                      (.splitExp 0 10
                        (.missing 0 23)
                        (.reject))
                      (.reject))
                    (.step (.primeLo 3 613) <|
                    .step (.dropHi 2 438) <|
                    .step (.primeHi 2 433) <|
                    .step (.dropLo 3 617) <|
                    .splitExp 1 6
                      (.splitExp 0 10
                        (.missing 0 23)
                        (.reject))
                      (.reject)))))
              (.use 0))))
        (.use 1)))

private def deficientFourPowerGeneralPart084Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,448,467,2,0⟩, ⟨false,563,619,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart082⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,389,467,2,0⟩, ⟨false,640,743,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart083⟩]

theorem deficientFourPowerGeneralPart084 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,331,467,2,0⟩, ⟨false,563,749,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart084Tree deficientFourPowerGeneralPart084Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
