module

public import OddPerfect.DeficientPowerReplayGeneral.Part008

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart040Tree : Tree :=
  .step (.dropLo 4 398) <|
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
          .step (.dropHi 4 453) <|
          .splitBase 3 589
            (.step (.primeHi 3 587) <|
            .step (.dropLo 4 449) <|
            .splitExp 1 6
              (.step (.dropHi 4 450) <|
              .step (.xHi 449) <|
              .reject)
              (.step (.dropLo 4 451) <|
              .step (.xLo 453) <|
              .missing 4 227))
            (.step (.primeLo 3 593) <|
            .step (.dropHi 4 449) <|
            .splitExp 1 6
              (.step (.dropHi 4 447) <|
              .step (.xHi 445) <|
              .missing 4 223)
              (.step (.dropLo 4 448) <|
              .step (.xLo 449) <|
              .splitExp 0 10
                (.missing 0 23)
                (.reject))))))
      (.step (.primeLo 3 599) <|
      .step (.dropHi 4 446) <|
      .step (.xHi 445) <|
      .splitExp 0 8
        (.step (.grow 0 13) <|
        .missing 0 757)
        (.step (.dropLo 4 432) <|
        .step (.xLo 433) <|
        .splitBase 3 607
          (.step (.dropLo 4 438) <|
          .step (.xLo 441) <|
          .splitBase 3 601
            (.splitExp 1 6
              (.step (.dropHi 4 443) <|
              .step (.xHi 441) <|
              .missing 4 13)
              (.step (.dropLo 4 443) <|
              .step (.xLo 445) <|
              .missing 4 223))
            (.step (.primeLo 3 607) <|
            .step (.dropHi 4 441) <|
            .missing 4 13))
          (.step (.primeLo 3 613) <|
          .step (.dropHi 4 438) <|
          .step (.xHi 437) <|
          .splitExp 1 6
            (.step (.dropHi 4 436) <|
            .step (.xHi 433) <|
            .missing 4 7)
            (.step (.dropLo 3 614) <|
            .step (.dropLo 4 434) <|
            .step (.primeLo 3 617) <|
            .step (.xLo 437) <|
            .missing 4 73)))))
    (.step (.primeLo 3 631) <|
    .step (.dropHi 4 430) <|
    .step (.xHi 429) <|
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
          .splitBase 3 635
            (.step (.primeHi 3 631) <|
            .step (.dropLo 4 426) <|
            .step (.xLo 429) <|
            .missing 4 43)
            (.step (.primeLo 3 641) <|
            .step (.dropHi 4 425) <|
            .missing 4 71))
          (.step (.primeLo 3 643) <|
          .step (.dropHi 4 424) <|
          .step (.xHi 421) <|
          .splitBase 3 647
            (.step (.dropLo 4 419) <|
            .step (.xLo 421) <|
            .missing 4 211)
            (.step (.primeLo 3 653) <|
            .step (.dropHi 4 420) <|
            .step (.xHi 417) <|
            .missing 4 11))))
      (.step (.primeLo 3 659) <|
      .step (.dropHi 4 417) <|
      .splitExp 0 8
        (.missing 0 13)
        (.step (.dropLo 4 405) <|
        .splitBase 3 669
          (.step (.primeHi 3 661) <|
          .step (.dropLo 4 413) <|
          .splitExp 1 6
            (.step (.dropHi 4 415) <|
            .step (.xHi 413) <|
            .missing 4 23)
            (.step (.dropLo 4 415) <|
            .step (.xLo 417) <|
            .missing 4 11))
          (.step (.primeLo 3 673) <|
          .step (.dropHi 4 412) <|
          .step (.xHi 409) <|
          .splitBase 3 677
            (.step (.dropLo 4 407) <|
            .step (.xLo 409) <|
            .missing 4 41)
            (.step (.primeLo 3 683) <|
            .step (.dropHi 4 408) <|
            .step (.xHi 405) <|
            .missing 4 7)))))

theorem deficientFourPowerGeneralPart040 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,577,683,2,0⟩, ⟨true,369,457,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart040Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart041Tree : Tree :=
  .step (.primeLo 3 691) <|
  .step (.dropHi 4 406) <|
  .step (.xHi 405) <|
  .splitExp 1 4
    (.step (.grow 1 11) <|
    .missing 1 71)
    (.step (.dropLo 4 332) <|
    .step (.xLo 333) <|
    .splitBase 3 765
      (.step (.primeHi 3 761) <|
      .step (.dropLo 4 349) <|
      .splitExp 2 2
        (.missing 2 307)
        (.step (.dropLo 4 375) <|
        .step (.xLo 377) <|
        .splitBase 3 723
          (.step (.primeHi 3 719) <|
          .step (.dropLo 4 387) <|
          .step (.xLo 389) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 4 394) <|
            .step (.xLo 397) <|
            .step (.dropHi 3 718) <|
            .step (.primeHi 3 709) <|
            .splitBase 3 699
              (.step (.primeHi 3 691) <|
              .step (.dropLo 4 402) <|
              .step (.xLo 405) <|
              .missing 4 7)
              (.step (.primeLo 3 701) <|
              .step (.dropHi 4 402) <|
              .step (.xHi 401) <|
              .splitExp 1 6
                (.step (.dropHi 4 400) <|
                .step (.xHi 397) <|
                .missing 4 199)
                (.step (.dropLo 3 702) <|
                .step (.dropLo 4 399) <|
                .step (.primeLo 3 709) <|
                .step (.xLo 401) <|
                .missing 4 67))))
          (.step (.primeLo 3 727) <|
          .step (.dropHi 4 394) <|
          .step (.xHi 393) <|
          .splitExp 0 8
            (.step (.grow 0 13) <|
            .step (.fix 0 757 3) <|
            .step (.dropHi 4 378) <|
            .step (.xHi 377) <|
            .missing 4 7)
            (.step (.dropLo 4 382) <|
            .step (.xLo 385) <|
            .splitBase 3 743
              (.step (.dropLo 4 387) <|
              .step (.xLo 389) <|
              .splitBase 3 733
                (.splitExp 1 6
                  (.step (.dropHi 4 392) <|
                  .step (.xHi 389) <|
                  .missing 4 13)
                  (.step (.dropLo 3 728) <|
                  .step (.dropLo 4 391) <|
                  .step (.primeLo 3 733) <|
                  .step (.xLo 393) <|
                  .missing 4 197))
                (.step (.primeLo 3 739) <|
                .step (.dropHi 4 391) <|
                .step (.xHi 389) <|
                .missing 4 13))
              (.step (.primeLo 3 751) <|
              .step (.dropHi 4 387) <|
              .step (.xHi 385) <|
              .missing 4 193)))))
      (.step (.primeLo 3 769) <|
      .step (.dropHi 4 383) <|
      .step (.xHi 381) <|
      .splitExp 2 2
        (.missing 2 307)
        (.step (.dropLo 4 355) <|
        .step (.xLo 357) <|
        .splitBase 3 811
          (.step (.dropLo 4 364) <|
          .step (.xLo 365) <|
          .splitExp 0 8
            (.step (.grow 0 13) <|
            .missing 0 757)
            (.step (.dropLo 4 370) <|
            .step (.xLo 373) <|
            .splitBase 3 789
              (.step (.primeHi 3 787) <|
              .step (.dropLo 4 376) <|
              .step (.xLo 377) <|
              .splitBase 3 777
                (.step (.primeHi 3 773) <|
                .step (.dropLo 4 379) <|
                .step (.xLo 381) <|
                .missing 4 191)
                (.step (.primeLo 3 787) <|
                .step (.dropHi 4 378) <|
                .step (.xHi 377) <|
                .missing 4 7))
              (.step (.primeLo 3 797) <|
              .step (.dropHi 4 376) <|
              .step (.xHi 373) <|
              .missing 4 11)))
          (.step (.primeLo 3 821) <|
          .step (.dropHi 4 371) <|
          .step (.xHi 369) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 4 361) <|
            .splitBase 3 839
              (.step (.dropLo 4 365) <|
              .splitBase 3 829
                (.step (.dropLo 4 367) <|
                .step (.xLo 369) <|
                .missing 4 37)
                (.step (.primeLo 3 839) <|
                .step (.dropHi 4 367) <|
                .step (.xHi 365) <|
                .missing 4 61))
              (.step (.primeLo 3 853) <|
              .step (.dropHi 4 365) <|
              .splitExp 1 6
                (.step (.dropHi 4 363) <|
                .step (.xHi 361) <|
                .missing 4 181)
                (.step (.dropLo 4 363) <|
                .step (.xLo 365) <|
                .missing 4 61)))))))

theorem deficientFourPowerGeneralPart041 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,690,859,2,0⟩, ⟨true,301,457,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart041Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart042Tree : Tree :=
  .step (.primeHi 3 859) <|
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
            (.step (.primeHi 3 457) <|
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
                      (.step (.dropHi 4 624) <|
                      .step (.xHi 621) <|
                      .splitBase 3 431
                        (.reject)
                        (.step (.primeLo 3 433) <|
                        .step (.dropHi 4 619) <|
                        .step (.xHi 617) <|
                        .missing 4 103))
                      (.step (.dropLo 4 622) <|
                      .step (.xLo 625) <|
                      .step (.dropHi 3 432) <|
                      .step (.primeHi 3 431) <|
                      .step (.dropLo 4 626) <|
                      .step (.xLo 629) <|
                      .missing 4 7))
                    (.step (.primeLo 3 439) <|
                    .step (.dropHi 4 612) <|
                    .step (.xHi 609) <|
                    .splitBase 3 439
                      (.step (.dropLo 4 605) <|
                      .splitExp 1 6
                        (.step (.dropHi 4 607) <|
                        .step (.xHi 605) <|
                        .missing 4 101)
                        (.reject))
                      (.step (.primeLo 3 443) <|
                      .step (.dropHi 4 605) <|
                      .splitExp 1 6
                        (.reject)
                        (.step (.dropLo 4 602) <|
                        .step (.xLo 605) <|
                        .missing 4 101)))))
                (.step (.primeLo 3 449) <|
                .step (.dropHi 4 594) <|
                .step (.xHi 593) <|
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
                      (.step (.dropHi 4 589) <|
                      .missing 4 59)
                      (.step (.dropLo 4 591) <|
                      .step (.xLo 593) <|
                      .missing 4 11))
                    (.step (.primeLo 3 457) <|
                    .step (.dropHi 4 580) <|
                    .step (.xHi 577) <|
                    .splitExp 1 6
                      (.reject)
                      (.reject))))))
            (.use 0)))
        (.use 1)))
    (.step (.primeLo 3 577) <|
    .step (.dropHi 4 459) <|
    .step (.xHi 457) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 4 301) <|
      .splitBase 3 689
        (.step (.primeHi 3 683) <|
        .step (.dropLo 4 331) <|
        .step (.xLo 333) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .missing 1 71)
          (.step (.dropLo 4 368) <|
          .step (.xLo 369) <|
          .splitExp 2 2
            (.missing 2 307)
            (.use 2)))
        (.use 3)))

private def deficientFourPowerGeneralPart042Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,460,491,2,0⟩, ⟨true,469,629,5,0⟩], 1, deficientFourPowerGeneralPart038⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,492,571,2,0⟩, ⟨true,369,629,5,0⟩], 1, deficientFourPowerGeneralPart039⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,577,683,2,0⟩, ⟨true,369,457,5,0⟩], 1, deficientFourPowerGeneralPart040⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,690,859,2,0⟩, ⟨true,301,457,5,0⟩], 1, deficientFourPowerGeneralPart041⟩]

theorem deficientFourPowerGeneralPart042 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,431,861,2,0⟩, ⟨true,205,629,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart042Tree deficientFourPowerGeneralPart042Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart043Tree : Tree :=
  .step (.primeLo 3 983) <|
  .step (.dropHi 4 345) <|
  .splitExp 2 2
    (.missing 2 307)
    (.step (.dropLo 4 323) <|
    .step (.xLo 325) <|
    .splitBase 3 1049
      (.step (.dropLo 4 331) <|
      .step (.xLo 333) <|
      .splitExp 0 8
        (.missing 0 13)
        (.step (.dropLo 4 336) <|
        .step (.xLo 337) <|
        .splitBase 3 1013
          (.step (.dropLo 4 340) <|
          .step (.xLo 341) <|
          .splitBase 3 997
            (.splitExp 1 6
              (.step (.dropHi 4 344) <|
              .step (.xHi 341) <|
              .missing 4 19)
              (.step (.dropLo 4 343) <|
              .step (.xLo 345) <|
              .missing 4 173))
            (.step (.primeLo 3 1009) <|
            .step (.dropHi 4 342) <|
            .step (.xHi 341) <|
            .missing 4 19))
          (.step (.primeLo 3 1019) <|
          .step (.dropHi 4 341) <|
          .splitBase 3 1033
            (.splitExp 1 6
              (.step (.dropHi 4 340) <|
              .step (.xHi 337) <|
              .missing 4 13)
              (.step (.dropLo 4 339) <|
              .step (.xLo 341) <|
              .missing 4 19))
            (.step (.primeLo 3 1039) <|
            .step (.dropHi 4 339) <|
            .step (.xHi 337) <|
            .missing 4 13))))
      (.step (.primeLo 3 1051) <|
      .step (.dropHi 4 338) <|
      .step (.xHi 337) <|
      .splitExp 0 8
        (.step (.grow 0 13) <|
        .missing 0 757)
        (.step (.dropLo 4 328) <|
        .step (.xLo 329) <|
        .splitBase 3 1087
          (.step (.dropLo 4 332) <|
          .step (.xLo 333) <|
          .splitBase 3 1067
            (.step (.primeHi 3 1063) <|
            .step (.dropLo 4 334) <|
            .step (.xLo 337) <|
            .missing 4 13)
            (.step (.primeLo 3 1069) <|
            .step (.dropHi 4 336) <|
            .step (.xHi 333) <|
            .missing 4 167))
          (.step (.primeLo 3 1091) <|
          .step (.dropHi 4 334) <|
          .step (.xHi 333) <|
          .splitBase 3 1109
            (.step (.dropLo 4 330) <|
            .step (.xLo 333) <|
            .missing 4 167)
            (.step (.primeLo 3 1117) <|
            .step (.dropHi 4 331) <|
            .step (.xHi 329) <|
            .missing 4 11)))))

theorem deficientFourPowerGeneralPart043 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,978,1129,2,0⟩, ⟨true,305,361,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart043Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart044Tree : Tree :=
  .step (.primeLo 3 1381) <|
  .step (.dropHi 4 314) <|
  .step (.xHi 313) <|
  .splitExp 2 2
    (.missing 2 307)
    (.step (.dropLo 4 294) <|
    .step (.xLo 297) <|
    .splitBase 3 1533
      (.step (.primeHi 3 1531) <|
      .step (.dropLo 4 301) <|
      .splitBase 3 1451
        (.step (.dropLo 4 304) <|
        .step (.xLo 305) <|
        .splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 4 308) <|
          .step (.xLo 309) <|
          .splitBase 3 1415
            (.step (.primeHi 3 1409) <|
            .step (.dropLo 4 310) <|
            .step (.xLo 313) <|
            .missing 4 157)
            (.step (.primeLo 3 1423) <|
            .step (.dropHi 4 311) <|
            .step (.xHi 309) <|
            .missing 4 31)))
        (.step (.primeLo 3 1453) <|
        .step (.dropHi 4 310) <|
        .step (.xHi 309) <|
        .splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 4 305) <|
          .splitBase 3 1489
            (.step (.dropLo 4 307) <|
            .step (.xLo 309) <|
            .missing 4 31)
            (.step (.primeLo 3 1493) <|
            .step (.dropHi 4 308) <|
            .step (.xHi 305) <|
            .reject))))
      (.step (.primeLo 3 1543) <|
      .step (.dropHi 4 306) <|
      .step (.xHi 305) <|
      .splitBase 3 1627
        (.splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 4 301) <|
          .splitBase 3 1583
            (.step (.dropLo 4 303) <|
            .step (.xLo 305) <|
            .splitExp 1 6
              (.step (.dropHi 3 1556) <|
              .step (.primeHi 3 1553) <|
              .splitExp 0 10
                (.missing 0 23)
                (.reject))
              (.step (.dropLo 3 1571) <|
              .splitExp 0 10
                (.missing 0 23)
                (.reject)))
            (.step (.primeLo 3 1597) <|
            .step (.dropHi 4 304) <|
            .step (.xHi 301) <|
            .missing 4 151)))
        (.step (.primeLo 3 1637) <|
        .step (.dropHi 4 303) <|
        .step (.xHi 301) <|
        .splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 3 1652) <|
          .step (.dropLo 4 298) <|
          .step (.primeLo 3 1657) <|
          .step (.xLo 301) <|
          .missing 4 151))))

theorem deficientFourPowerGeneralPart044 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,1380,1723,2,0⟩, ⟨true,281,325,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart044Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
