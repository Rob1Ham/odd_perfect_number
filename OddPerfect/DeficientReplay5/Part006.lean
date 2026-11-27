module

public import OddPerfect.DeficientReplay5.Part005

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour5Part025Tree : Tree :=
  .step (.primeLo 3 283) <|
  .step (.dropHi 4 2672) <|
  .step (.xHi 2669) <|
  .splitBase 3 337
    (.step (.dropLo 4 520) <|
    .step (.xLo 521) <|
    .splitExp 0 6
      (.step (.grow 0 1093) <|
      .step (.dropHi 4 1202) <|
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
            .step (.dropHi 4 1535) <|
            .step (.xHi 1533) <|
            .splitExp 2 2
              (.step (.dropHi 4 1169) <|
              .splitExp 0 8
                (.step (.grow 0 13) <|
                .missing 0 757)
                (.step (.dropLo 4 1145) <|
                .splitExp 1 6
                  (.step (.dropHi 4 1152) <|
                  .step (.xHi 1149) <|
                  .splitExp 0 10
                    (.missing 0 23)
                    (.reject))
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
                  (.step (.dropHi 4 1505) <|
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
        (.use 1)))
    (.step (.primeLo 3 347) <|
    .step (.dropHi 4 972) <|
    .step (.xHi 969) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 4 474) <|
      .step (.xLo 477) <|
      .splitBase 3 379
        (.step (.dropLo 4 542) <|
        .step (.xLo 545) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .step (.grow 1 71) <|
          .step (.dropHi 4 741) <|
          .step (.xLo 781) <|
          .reject)
          (.step (.dropLo 4 650) <|
          .step (.xLo 653) <|
          .splitExp 2 2
            (.step (.grow 2 307) <|
            .step (.dropHi 4 811) <|
            .step (.xLo 921) <|
            .reject)
            (.use 2)))
        (.use 3)))

private def deficientFour5Part025Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,283,293,2,0⟩, ⟨true,1089,2669,1,1⟩], 1, deficientFour5Part021⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,308,337,2,0⟩, ⟨true,661,2669,1,1⟩], 1, deficientFour5Part022⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,379,2,0⟩, ⟨true,653,969,1,1⟩], 1, deficientFour5Part023⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,380,421,2,0⟩, ⟨true,477,969,1,1⟩], 1, deficientFour5Part024⟩]

theorem deficientFour5Part025 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,282,421,2,0⟩, ⟨true,397,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part025Tree deficientFour5Part025Refs _ _ (by decide +kernel)

private def deficientFour5Part026Tree : Tree :=
  .step (.dropLo 4 397) <|
  .splitBase 3 281
    (.step (.dropLo 4 752) <|
    .step (.xLo 753) <|
    .splitBase 3 241
      (.use 0)
      (.step (.primeLo 3 251) <|
      .splitExp 0 6
        (.step (.grow 0 1093) <|
        .step (.dropHi 4 2636) <|
        .step (.xLo 1093) <|
        .step (.xHi 1093) <|
        .missing 4 547)
        (.step (.dropLo 4 1083) <|
        .step (.xLo 1085) <|
        .splitBase 3 265
          (.step (.primeHi 3 263) <|
          .step (.dropLo 4 1473) <|
          .splitExp 1 4
            (.step (.grow 1 11) <|
            .step (.grow 1 71) <|
            .step (.dropHi 4 4132) <|
            .step (.xLo 3905) <|
            .step (.xHi 3905) <|
            .missing 4 7)
            (.step (.dropLo 4 2691) <|
            .step (.xLo 2693) <|
            .splitExp 2 2
              (.step (.grow 2 307) <|
              .step (.dropHi 4 7971) <|
              .step (.xLo 3377) <|
              .step (.xHi 7061) <|
              .step (.dropHi 3 262) <|
              .step (.primeHi 3 257) <|
              .step (.dropLo 4 3540) <|
              .step (.xLo 4605) <|
              .step (.dropHi 3 256) <|
              .step (.primeHi 3 251) <|
              .step (.dropLo 4 5288) <|
              .step (.xLo 5833) <|
              .splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 4 6947) <|
                .step (.xLo 7061) <|
                .missing 4 11))
              (.step (.dropLo 4 5926) <|
              .step (.xLo 5929) <|
              .splitBase 3 255
                (.step (.primeHi 3 251) <|
                .reject)
                (.step (.primeLo 3 257) <|
                .step (.dropHi 4 65535) <|
                .step (.xHi 65533) <|
                .splitBase 3 259
                  (.use 1)
                  (.step (.primeLo 3 263) <|
                  .step (.dropHi 4 9580) <|
                  .step (.xHi 9577) <|
                  .splitExp 0 8
                    (.step (.grow 0 13) <|
                    .missing 0 757)
                    (.step (.dropLo 4 8092) <|
                    .step (.xLo 8093) <|
                    .splitExp 1 6
                      (.step (.dropHi 4 8534) <|
                      .step (.xHi 8533) <|
                      .splitExp 0 10
                        (.step (.grow 0 23) <|
                        .step (.dropHi 4 8141) <|
                        .step (.xLo 8165) <|
                        .reject)
                        (.step (.dropLo 4 8435) <|
                        .step (.xLo 8437) <|
                        .splitExp 2 4
                          (.step (.dropHi 4 8483) <|
                          .step (.xHi 8481) <|
                          .splitExp 0 12
                            (.step (.dropHi 4 8438) <|
                            .step (.xHi 8437) <|
                            .last 3)
                            (.step (.dropLo 4 8475) <|
                            .step (.xLo 8477) <|
                            .splitExp 0 14
                              (.step (.grow 0 11) <|
                              .missing 0 13)
                              (.step (.dropLo 4 8479) <|
                              .step (.xLo 8481) <|
                              .splitExp 3 2
                                (.missing 3 7)
                                (.reject))))
                          (.step (.dropLo 4 8485) <|
                          .splitExp 0 12
                            (.step (.dropHi 4 8488) <|
                            .step (.xHi 8485) <|
                            .splitExp 3 2
                              (.missing 3 7)
                              (.reject))
                            (.step (.dropLo 4 8525) <|
                            .splitExp 0 14
                              (.step (.grow 0 11) <|
                              .missing 0 13)
                              (.step (.dropLo 4 8530) <|
                              .step (.xLo 8533) <|
                              .missing 4 251)))))
                      (.use 2)))))))
          (.use 3))))
    (.use 4)

private def deficientFour5Part026Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,211,241,2,0⟩, ⟨true,753,0,1,1⟩], 1, deficientFour5Part013⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,259,2,0⟩, ⟨true,5929,65533,1,1⟩], 1, deficientFour5Part016⟩,
  ⟨#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,8093,9577,1,1⟩], 1, deficientFour5Part017⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,266,281,2,0⟩, ⟨true,1085,0,1,1⟩], 1, deficientFour5Part020⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,282,421,2,0⟩, ⟨true,397,0,1,1⟩], 1, deficientFour5Part025⟩]

theorem deficientFour5Part026 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,211,421,2,0⟩, ⟨true,205,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part026Tree deficientFour5Part026Refs _ _ (by decide +kernel)

private def deficientFour5Part027Tree : Tree :=
  .step (.primeHi 3 457) <|
  .step (.dropLo 4 502) <|
  .step (.xLo 505) <|
  .splitExp 2 2
    (.missing 2 307)
    (.step (.dropLo 4 559) <|
    .step (.xLo 561) <|
    .splitBase 3 443
      (.step (.dropLo 4 582) <|
      .step (.xLo 585) <|
      .splitExp 0 8
        (.step (.grow 0 13) <|
        .missing 0 757)
        (.step (.dropLo 4 598) <|
        .step (.xLo 601) <|
        .splitBase 3 435
          (.step (.primeHi 3 433) <|
          .step (.dropLo 4 617) <|
          .splitExp 1 6
            (.step (.dropHi 4 623) <|
            .step (.xHi 621) <|
            .splitBase 3 431
              (.step (.dropLo 4 621) <|
              .missing 4 311)
              (.step (.primeLo 3 433) <|
              .step (.dropHi 4 618) <|
              .step (.xHi 617) <|
              .missing 4 103))
            (.step (.dropLo 4 622) <|
            .step (.xLo 625) <|
            .missing 4 313))
          (.step (.primeLo 3 439) <|
          .step (.dropHi 4 611) <|
          .step (.xHi 609) <|
          .splitBase 3 439
            (.step (.dropLo 4 605) <|
            .splitExp 1 6
              (.step (.dropHi 4 606) <|
              .step (.xHi 605) <|
              .missing 4 101)
              (.reject))
            (.step (.primeLo 3 443) <|
            .step (.dropHi 4 604) <|
            .step (.xHi 601) <|
            .missing 4 7))))
      (.step (.primeLo 3 449) <|
      .step (.dropHi 4 593) <|
      .splitExp 0 8
        (.step (.grow 0 13) <|
        .missing 0 757)
        (.step (.dropLo 4 574) <|
        .step (.xLo 577) <|
        .splitBase 3 451
          (.step (.primeHi 3 449) <|
          .step (.dropLo 4 587) <|
          .step (.xLo 589) <|
          .splitExp 1 6
            (.reject)
            (.step (.dropLo 4 591) <|
            .step (.xLo 593) <|
            .missing 4 11))
          (.step (.primeLo 3 457) <|
          .step (.dropHi 4 579) <|
          .step (.xHi 577) <|
          .splitExp 1 6
            (.reject)
            (.reject)))))

theorem deficientFour5Part027 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,431,459,2,0⟩, ⟨true,469,625,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part027Tree [] _ _ (by decide +kernel)

private def deficientFour5Part028Tree : Tree :=
  .step (.primeLo 3 499) <|
  .step (.dropHi 4 523) <|
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
                (.step (.dropHi 3 501) <|
                .step (.dropHi 4 520) <|
                .step (.primeHi 3 499) <|
                .step (.xHi 517) <|
                .missing 4 7)
                (.step (.dropLo 4 518) <|
                .step (.xLo 521) <|
                .missing 4 29))
              (.step (.primeLo 3 509) <|
              .step (.dropHi 4 513) <|
              .splitExp 1 6
                (.step (.dropHi 4 509) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.reject))
                (.step (.dropLo 4 512) <|
                .step (.xLo 513) <|
                .missing 4 257))))
          (.step (.primeLo 3 521) <|
          .step (.dropHi 4 501) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 4 495) <|
            .step (.xLo 497) <|
            .splitExp 1 6
              (.step (.dropHi 3 522) <|
              .step (.dropHi 4 498) <|
              .step (.primeHi 3 521) <|
              .step (.xHi 497) <|
              .missing 4 83)
              (.step (.dropLo 4 498) <|
              .step (.xLo 501) <|
              .missing 4 251))))
        (.step (.primeLo 3 541) <|
        .step (.dropHi 4 484) <|
        .step (.xHi 481) <|
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
              .missing 4 241)
              (.step (.primeLo 3 547) <|
              .step (.dropHi 4 479) <|
              .step (.xHi 477) <|
              .missing 4 239)))
          (.step (.primeLo 3 557) <|
          .step (.dropHi 4 471) <|
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
                .step (.dropHi 4 467) <|
                .step (.xHi 465) <|
                .missing 4 233))
              (.step (.primeLo 3 569) <|
              .step (.dropHi 4 463) <|
              .step (.xHi 461) <|
              .missing 4 7))))))

theorem deficientFour5Part028 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,492,571,2,0⟩, ⟨true,369,625,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part028Tree [] _ _ (by decide +kernel)

private def deficientFour5Part029Tree : Tree :=
  .step (.primeHi 3 683) <|
  .step (.dropLo 4 331) <|
  .step (.xLo 333) <|
  .splitExp 1 4
    (.step (.grow 1 11) <|
    .missing 1 71)
    (.step (.dropLo 4 368) <|
    .step (.xLo 369) <|
    .splitExp 2 2
      (.missing 2 307)
      (.step (.dropLo 4 398) <|
      .step (.xLo 401) <|
      .splitBase 3 625
        (.step (.primeHi 3 619) <|
        .step (.dropLo 4 423) <|
        .step (.xLo 425) <|
        .splitBase 3 597
          (.step (.primeHi 3 593) <|
          .step (.dropLo 4 437) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 4 445) <|
            .splitBase 3 583
              (.step (.primeHi 3 577) <|
              .step (.dropLo 4 455) <|
              .step (.xLo 457) <|
              .missing 4 229)
              (.step (.primeLo 3 587) <|
              .step (.dropHi 4 452) <|
              .step (.xHi 449) <|
              .splitBase 3 589
                (.step (.primeHi 3 587) <|
                .step (.dropLo 4 449) <|
                .splitExp 1 6
                  (.splitExp 0 10
                    (.missing 0 23)
                    (.reject))
                  (.reject))
                (.step (.primeLo 3 593) <|
                .step (.dropHi 4 448) <|
                .step (.xHi 445) <|
                .missing 4 223))))
          (.step (.primeLo 3 599) <|
          .step (.dropHi 4 445) <|
          .splitExp 0 8
            (.step (.grow 0 13) <|
            .missing 0 757)
            (.step (.dropLo 4 432) <|
            .step (.xLo 433) <|
            .splitBase 3 607
              (.step (.dropLo 4 438) <|
              .step (.xLo 441) <|
              .step (.dropHi 3 606) <|
              .step (.primeHi 3 601) <|
              .splitExp 1 6
                (.step (.dropHi 4 442) <|
                .step (.xHi 441) <|
                .missing 4 13)
                (.step (.dropLo 4 443) <|
                .step (.xLo 445) <|
                .missing 4 223))
              (.step (.primeLo 3 613) <|
              .step (.dropHi 4 437) <|
              .splitExp 1 6
                (.step (.dropHi 3 617) <|
                .step (.dropHi 4 435) <|
                .step (.xHi 433) <|
                .missing 4 7)
                (.step (.dropLo 4 434) <|
                .step (.xLo 437) <|
                .missing 4 73)))))
        (.step (.primeLo 3 631) <|
        .step (.dropHi 4 429) <|
        .splitBase 3 655
          (.step (.primeHi 3 653) <|
          .step (.dropLo 4 409) <|
          .splitExp 0 8
            (.step (.grow 0 13) <|
            .missing 0 757)
            (.step (.dropLo 4 417) <|
            .splitBase 3 641
              (.step (.dropLo 4 422) <|
              .step (.xLo 425) <|
              .step (.dropHi 3 640) <|
              .step (.primeHi 3 631) <|
              .step (.dropLo 4 426) <|
              .step (.xLo 429) <|
              .missing 4 43)
              (.step (.primeLo 3 643) <|
              .step (.dropHi 4 423) <|
              .step (.xHi 421) <|
              .splitBase 3 647
                (.step (.dropLo 4 419) <|
                .step (.xLo 421) <|
                .missing 4 211)
                (.step (.primeLo 3 653) <|
                .step (.dropHi 4 419) <|
                .step (.xHi 417) <|
                .missing 4 11))))
          (.step (.primeLo 3 659) <|
          .step (.dropHi 4 416) <|
          .step (.xHi 413) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 3 660) <|
            .step (.dropLo 4 405) <|
            .step (.primeLo 3 661) <|
            .splitBase 3 671
              (.step (.primeHi 3 661) <|
              .step (.dropLo 4 413) <|
              .missing 4 23)
              (.step (.primeLo 3 673) <|
              .step (.dropHi 4 411) <|
              .step (.xHi 409) <|
              .splitBase 3 677
                (.step (.dropLo 4 407) <|
                .step (.xLo 409) <|
                .missing 4 41)
                (.step (.primeLo 3 683) <|
                .step (.dropHi 4 407) <|
                .step (.xHi 405) <|
                .missing 4 7)))))))

theorem deficientFour5Part029 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,577,689,2,0⟩, ⟨true,301,457,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part029Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
