module

public import OddPerfect.DeficientPowerReplayGeneral.Part007

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart035Tree : Tree :=
  .step (.dropLo 4 520) <|
  .step (.xLo 521) <|
  .splitExp 0 6
    (.step (.grow 0 1093) <|
    .step (.dropHi 4 1203) <|
    .step (.xLo 1093) <|
    .step (.xHi 1093) <|
    .missing 4 547)
    (.step (.dropLo 4 659) <|
    .step (.xLo 661) <|
    .splitBase 3 307
      (.step (.dropLo 4 816) <|
      .step (.xLo 817) <|
      .splitExp 1 4
        (.step (.grow 1 11) <|
        .missing 1 71)
        (.step (.dropLo 4 1089) <|
        .splitBase 3 293
          (.use 0)
          (.step (.primeLo 3 307) <|
          .step (.dropHi 4 1536) <|
          .step (.xHi 1533) <|
          .splitExp 2 2
            (.step (.dropHi 4 1170) <|
            .step (.xHi 1169) <|
            .splitExp 0 8
              (.step (.grow 0 13) <|
              .missing 0 757)
              (.step (.dropLo 4 1145) <|
              .splitExp 1 6
                (.step (.dropHi 4 1153) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 4 1152) <|
                  .step (.xLo 1153) <|
                  .missing 4 577))
                (.step (.dropLo 4 1161) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 4 1168) <|
                  .step (.xLo 1169) <|
                  .missing 4 13))))
            (.step (.dropLo 4 1397) <|
            .splitExp 0 8
              (.step (.grow 0 13) <|
              .missing 0 757)
              (.step (.dropLo 4 1492) <|
              .step (.xLo 1493) <|
              .splitExp 1 6
                (.step (.dropHi 4 1506) <|
                .step (.xHi 1505) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 4 1503) <|
                  .step (.xLo 1505) <|
                  .missing 4 251))
                (.step (.dropLo 4 1519) <|
                .step (.xLo 1521) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 4 1531) <|
                  .step (.xLo 1533) <|
                  .missing 4 13)))))))
      (.step (.primeLo 3 311) <|
      .step (.dropHi 4 1442) <|
      .step (.xHi 1441) <|
      .splitExp 1 4
        (.step (.grow 1 11) <|
        .step (.grow 1 71) <|
        .step (.dropHi 4 987) <|
        .step (.xLo 781) <|
        .step (.xHi 781) <|
        .missing 4 23)
        (.step (.dropLo 4 827) <|
        .step (.xLo 829) <|
        .splitExp 2 2
          (.step (.grow 2 307) <|
          .step (.dropHi 4 1115) <|
          .step (.xLo 921) <|
          .step (.xHi 921) <|
          .missing 4 461)
          (.use 1))))

private def deficientFourPowerGeneralPart035Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,283,293,2,0⟩, ⟨true,1089,2673,5,0⟩], 1, deficientFourPowerGeneralPart033⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,311,337,2,0⟩, ⟨true,829,1441,5,0⟩], 1, deficientFourPowerGeneralPart034⟩]

theorem deficientFourPowerGeneralPart035 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,283,337,2,0⟩, ⟨true,397,2673,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart035Tree deficientFourPowerGeneralPart035Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart036Tree : Tree :=
  .step (.primeHi 3 359) <|
  .step (.dropLo 4 841) <|
  .splitBase 3 351
    (.step (.primeHi 3 349) <|
    .step (.dropLo 4 902) <|
    .step (.xLo 905) <|
    .splitExp 0 8
      (.step (.grow 0 13) <|
      .missing 0 757)
      (.step (.dropLo 4 940) <|
      .step (.xLo 941) <|
      .splitExp 1 6
        (.step (.dropHi 4 961) <|
        .splitBase 3 347
          (.step (.dropLo 4 955) <|
          .step (.xLo 957) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 4 960) <|
            .step (.xLo 961) <|
            .missing 4 13))
          (.step (.primeLo 3 349) <|
          .step (.dropHi 4 946) <|
          .step (.xHi 945) <|
          .splitExp 0 10
            (.missing 0 23)
            (.reject)))
        (.step (.dropLo 4 951) <|
        .step (.xLo 953) <|
        .splitBase 3 347
          (.step (.dropLo 4 966) <|
          .step (.xLo 969) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 4 971) <|
            .step (.xLo 973) <|
            .missing 4 487))
          (.step (.primeLo 3 349) <|
          .step (.dropHi 4 957) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 4 956) <|
            .step (.xLo 957) <|
            .missing 4 479)))))
    (.step (.primeLo 3 353) <|
    .step (.dropHi 4 928) <|
    .step (.xHi 925) <|
    .splitExp 0 8
      (.step (.grow 0 13) <|
      .missing 0 757)
      (.step (.dropLo 4 874) <|
      .step (.xLo 877) <|
      .splitBase 3 355
        (.step (.primeHi 3 353) <|
        .step (.dropLo 4 912) <|
        .step (.xLo 913) <|
        .splitExp 1 6
          (.step (.dropHi 4 918) <|
          .step (.xHi 917) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 4 916) <|
            .step (.xLo 917) <|
            .splitExp 2 4
              (.splitExp 0 12
                (.reject)
                (.reject))
              (.reject)))
          (.step (.dropLo 4 923) <|
          .step (.xLo 925) <|
          .missing 4 463))
        (.step (.primeLo 3 359) <|
        .step (.dropHi 4 889) <|
        .splitExp 1 6
          (.step (.dropHi 4 879) <|
          .step (.xHi 877) <|
          .missing 4 439)
          (.step (.dropLo 4 884) <|
          .step (.xLo 885) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 4 888) <|
            .step (.xLo 889) <|
            .missing 4 89)))))

theorem deficientFourPowerGeneralPart036 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,361,2,0⟩, ⟨true,749,973,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart036Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart037Tree : Tree :=
  .step (.primeLo 3 383) <|
  .step (.dropHi 4 770) <|
  .step (.xHi 769) <|
  .splitExp 1 4
    (.step (.grow 1 11) <|
    .missing 1 71)
    (.step (.dropLo 4 555) <|
    .step (.xLo 557) <|
    .splitExp 2 2
      (.missing 2 307)
      (.step (.dropLo 4 625) <|
      .splitBase 3 401
        (.step (.dropLo 4 675) <|
        .step (.xLo 677) <|
        .splitBase 3 391
          (.step (.primeHi 3 389) <|
          .step (.dropLo 4 712) <|
          .step (.xLo 713) <|
          .splitExp 0 8
            (.step (.grow 0 13) <|
            .missing 0 757)
            (.step (.dropLo 4 736) <|
            .step (.xLo 737) <|
            .splitBase 3 385
              (.step (.primeHi 3 383) <|
              .step (.dropLo 4 758) <|
              .step (.xLo 761) <|
              .splitExp 1 6
                (.step (.dropHi 4 762) <|
                .step (.xHi 761) <|
                .missing 4 127)
                (.step (.dropLo 4 765) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 4 768) <|
                  .step (.xLo 769) <|
                  .missing 4 7)))
              (.step (.primeLo 3 389) <|
              .step (.dropHi 4 746) <|
              .step (.xHi 745) <|
              .splitExp 1 6
                (.step (.dropHi 4 739) <|
                .step (.xHi 737) <|
                .missing 4 41)
                (.step (.dropLo 4 743) <|
                .step (.xLo 745) <|
                .missing 4 373))))
          (.step (.primeLo 3 397) <|
          .step (.dropHi 4 718) <|
          .step (.xHi 717) <|
          .splitExp 0 8
            (.step (.grow 0 13) <|
            .missing 0 757)
            (.step (.dropLo 4 696) <|
            .step (.xLo 697) <|
            .splitBase 3 397
              (.step (.dropLo 4 709) <|
              .splitExp 1 6
                (.step (.dropHi 4 712) <|
                .step (.xHi 709) <|
                .missing 4 71)
                (.step (.dropLo 4 715) <|
                .step (.xLo 717) <|
                .missing 4 359))
              (.step (.primeLo 3 401) <|
              .step (.dropHi 4 706) <|
              .step (.xHi 705) <|
              .splitExp 1 6
                (.step (.dropHi 4 699) <|
                .step (.xHi 697) <|
                .missing 4 349)
                (.step (.dropLo 4 702) <|
                .step (.xLo 705) <|
                .missing 4 353)))))
        (.step (.primeLo 3 409) <|
        .step (.dropHi 4 682) <|
        .step (.xHi 681) <|
        .splitBase 3 413
          (.step (.primeHi 3 409) <|
          .step (.dropLo 4 653) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 4 673) <|
            .splitExp 1 6
              (.step (.dropHi 4 676) <|
              .step (.xHi 673) <|
              .missing 4 337)
              (.step (.dropLo 4 679) <|
              .step (.xLo 681) <|
              .missing 4 11)))
          (.step (.primeLo 3 419) <|
          .step (.dropHi 4 656) <|
          .step (.xHi 653) <|
          .splitExp 0 8
            (.step (.grow 0 13) <|
            .missing 0 757)
            (.step (.dropLo 4 643) <|
            .step (.xLo 645) <|
            .splitExp 1 6
              (.step (.dropHi 4 651) <|
              .step (.xHi 649) <|
              .splitBase 3 419
                (.step (.dropLo 4 648) <|
                .step (.xLo 649) <|
                .missing 4 13)
                (.step (.primeLo 3 421) <|
                .step (.dropHi 4 646) <|
                .step (.xHi 645) <|
                .missing 4 19))
              (.step (.dropLo 4 648) <|
              .step (.xLo 649) <|
              .splitBase 3 419
                (.reject)
                (.step (.primeLo 3 421) <|
                .step (.dropHi 4 651) <|
                .step (.xHi 649) <|
                .missing 4 13)))))))

theorem deficientFourPowerGeneralPart037 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,380,421,2,0⟩, ⟨true,477,973,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart037Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart038Tree : Tree :=
  .step (.primeLo 3 461) <|
  .step (.dropHi 4 574) <|
  .step (.xHi 573) <|
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
            (.step (.dropHi 4 570) <|
            .step (.xHi 569) <|
            .splitBase 3 461
              (.step (.dropLo 4 568) <|
              .step (.xLo 569) <|
              .missing 4 19)
              (.step (.primeLo 3 463) <|
              .step (.dropHi 4 567) <|
              .step (.xHi 565) <|
              .missing 4 283))
            (.step (.dropLo 4 569) <|
            .splitBase 3 461
              (.step (.dropLo 4 572) <|
              .step (.xLo 573) <|
              .missing 4 7)
              (.step (.primeLo 3 463) <|
              .step (.dropHi 4 571) <|
              .step (.xHi 569) <|
              .missing 4 19)))
          (.step (.primeLo 3 467) <|
          .step (.dropHi 4 565) <|
          .splitExp 1 6
            (.step (.dropHi 4 561) <|
            .missing 4 281)
            (.step (.dropLo 4 563) <|
            .step (.xLo 565) <|
            .missing 4 283))))
      (.step (.primeLo 3 479) <|
      .step (.dropHi 4 548) <|
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
          .step (.dropHi 4 538) <|
          .step (.xHi 537) <|
          .splitExp 1 6
            (.step (.dropHi 4 534) <|
            .step (.xHi 533) <|
            .splitBase 3 487
              (.reject)
              (.step (.primeLo 3 491) <|
              .step (.dropHi 4 530) <|
              .step (.xHi 529) <|
              .missing 4 53))
            (.step (.dropLo 4 531) <|
            .step (.xLo 533) <|
            .splitBase 3 487
              (.step (.dropLo 4 536) <|
              .step (.xLo 537) <|
              .missing 4 269)
              (.step (.primeLo 3 491) <|
              .step (.dropHi 4 533) <|
              .missing 4 89))))))

theorem deficientFourPowerGeneralPart038 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,460,491,2,0⟩, ⟨true,469,629,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart038Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart039Tree : Tree :=
  .step (.primeLo 3 499) <|
  .step (.dropHi 4 524) <|
  .step (.xHi 521) <|
  .splitExp 1 4
    (.step (.grow 1 11) <|
    .missing 1 71)
    (.step (.dropLo 4 412) <|
    .step (.xLo 413) <|
    .splitExp 2 2
      (.missing 2 307)
      (.step (.dropLo 4 449) <|
      .splitBase 3 531
        (.step (.primeHi 3 523) <|
        .step (.dropLo 4 484) <|
        .step (.xLo 485) <|
        .splitBase 3 509
          (.step (.dropLo 4 497) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 4 509) <|
            .splitBase 3 503
              (.step (.dropLo 4 515) <|
              .step (.xLo 517) <|
              .splitExp 1 6
                (.step (.dropHi 3 502) <|
                .step (.primeHi 3 499) <|
                .step (.dropLo 4 519) <|
                .step (.xLo 521) <|
                .missing 4 29)
                (.step (.dropLo 3 500) <|
                .step (.dropLo 4 518) <|
                .step (.primeLo 3 503) <|
                .step (.xLo 521) <|
                .missing 4 29))
              (.step (.primeLo 3 509) <|
              .step (.dropHi 4 514) <|
              .step (.xHi 513) <|
              .splitExp 1 6
                (.step (.dropHi 4 510) <|
                .step (.xHi 509) <|
                .reject)
                (.step (.dropLo 4 512) <|
                .step (.xLo 513) <|
                .missing 4 257))))
          (.step (.primeLo 3 521) <|
          .step (.dropHi 4 502) <|
          .step (.xHi 501) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 4 495) <|
            .step (.xLo 497) <|
            .splitExp 1 6
              (.step (.dropHi 4 499) <|
              .step (.xHi 497) <|
              .missing 4 83)
              (.step (.dropLo 4 498) <|
              .step (.xLo 501) <|
              .missing 4 251))))
        (.step (.primeLo 3 541) <|
        .step (.dropHi 4 485) <|
        .splitBase 3 555
          (.step (.primeHi 3 547) <|
          .step (.dropLo 4 465) <|
          .splitExp 0 8
            (.step (.grow 0 13) <|
            .missing 0 757)
            (.step (.dropLo 4 475) <|
            .step (.xLo 477) <|
            .splitBase 3 543
              (.step (.primeHi 3 541) <|
              .step (.dropLo 4 480) <|
              .step (.xLo 481) <|
              .splitExp 1 6
                (.step (.dropHi 4 482) <|
                .step (.xHi 481) <|
                .missing 4 241)
                (.step (.dropLo 4 483) <|
                .step (.xLo 485) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.splitExp 2 4
                    (.reject)
                    (.splitExp 0 12
                      (.reject)
                      (.splitExp 1 8
                        (.missing 1 19)
                        (.reject))))))
              (.step (.primeLo 3 547) <|
              .step (.dropHi 4 480) <|
              .step (.xHi 477) <|
              .missing 4 239)))
          (.step (.primeLo 3 557) <|
          .step (.dropHi 4 472) <|
          .step (.xHi 469) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 4 459) <|
            .step (.xLo 461) <|
            .splitBase 3 563
              (.step (.dropLo 4 464) <|
              .step (.xLo 465) <|
              .splitBase 3 559
                (.step (.primeHi 3 557) <|
                .step (.dropLo 4 468) <|
                .step (.xLo 469) <|
                .missing 4 47)
                (.step (.primeLo 3 563) <|
                .step (.dropHi 4 468) <|
                .step (.xHi 465) <|
                .missing 4 233))
              (.step (.primeLo 3 569) <|
              .step (.dropHi 4 464) <|
              .step (.xHi 461) <|
              .missing 4 7))))))

theorem deficientFourPowerGeneralPart039 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,492,571,2,0⟩, ⟨true,369,629,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart039Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
