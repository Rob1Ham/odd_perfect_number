module

public import OddPerfect.DeficientReplay5.Part004

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour5Part020Tree : Tree :=
  .step (.primeLo 3 269) <|
  .step (.dropHi 4 5276) <|
  .step (.xHi 5273) <|
  .splitExp 1 4
    (.step (.grow 1 11) <|
    .step (.grow 1 71) <|
    .step (.dropHi 4 1962) <|
    .step (.xLo 3905) <|
    .reject)
    (.step (.dropLo 4 1623) <|
    .step (.xLo 1625) <|
    .splitExp 2 2
      (.step (.grow 2 307) <|
      .step (.dropHi 4 2543) <|
      .step (.xLo 2149) <|
      .step (.xHi 2149) <|
      .missing 4 43)
      (.step (.dropLo 4 2420) <|
      .step (.xLo 2421) <|
      .splitBase 3 273
        (.step (.primeHi 3 271) <|
        .step (.dropLo 4 3554) <|
        .step (.xLo 3557) <|
        .splitExp 0 8
          (.step (.grow 0 13) <|
          .missing 0 757)
          (.step (.dropLo 4 4233) <|
          .splitBase 3 269
            (.step (.dropLo 4 4792) <|
            .step (.xLo 4793) <|
            .splitExp 1 6
              (.step (.dropHi 4 4942) <|
              .step (.xHi 4941) <|
              .splitExp 0 10
                (.step (.grow 0 23) <|
                .step (.dropHi 4 4808) <|
                .step (.xLo 4853) <|
                .reject)
                (.step (.dropLo 4 4910) <|
                .step (.xLo 4913) <|
                .splitExp 2 4
                  (.step (.dropHi 4 4925) <|
                  .splitExp 0 12
                    (.reject)
                    (.step (.dropLo 4 4923) <|
                    .step (.xLo 4925) <|
                    .missing 4 821))
                  (.step (.dropLo 4 4927) <|
                  .step (.xLo 4929) <|
                  .splitExp 0 12
                    (.reject)
                    (.step (.dropLo 4 4940) <|
                    .step (.xLo 4941) <|
                    .missing 4 7))))
              (.step (.dropLo 4 5091) <|
              .step (.xLo 5093) <|
              .splitExp 0 10
                (.step (.grow 0 23) <|
                .step (.dropHi 4 5123) <|
                .step (.xLo 5129) <|
                .reject)
                (.step (.dropLo 4 5225) <|
                .splitExp 2 4
                  (.step (.dropHi 4 5256) <|
                  .step (.xHi 5253) <|
                  .splitExp 0 12
                    (.step (.dropHi 4 5239) <|
                    .step (.xHi 5237) <|
                    .splitExp 1 8
                      (.step (.grow 1 19) <|
                      .missing 1 31)
                      (.reject))
                    (.step (.dropLo 4 5240) <|
                    .step (.xLo 5241) <|
                    .splitExp 1 8
                      (.missing 1 19)
                      (.reject)))
                  (.step (.dropLo 4 5244) <|
                  .step (.xLo 5245) <|
                  .splitExp 0 12
                    (.step (.dropHi 4 5259) <|
                    .step (.xHi 5257) <|
                    .splitExp 1 8
                      (.missing 1 19)
                      (.reject))
                    (.step (.dropLo 4 5259) <|
                    .step (.xLo 5261) <|
                    .splitExp 1 8
                      (.missing 1 19)
                      (.step (.dropLo 4 5273) <|
                      .missing 4 293))))))
            (.use 0)))
        (.use 1)))

private def deficientFour5Part020Refs : List Known := [
  ⟨#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,270,271,2,0⟩, ⟨true,4233,5273,1,1⟩], 1, deficientFour5Part018⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,274,281,2,0⟩, ⟨true,2421,5273,1,1⟩], 1, deficientFour5Part019⟩]

theorem deficientFour5Part020 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,266,281,2,0⟩, ⟨true,1085,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part020Tree deficientFour5Part020Refs _ _ (by decide +kernel)

private def deficientFour5Part021Tree : Tree :=
  .step (.dropLo 4 1312) <|
  .step (.xLo 1313) <|
  .splitExp 2 2
    (.step (.grow 2 307) <|
    .step (.dropHi 4 1730) <|
    .step (.xLo 2149) <|
    .reject)
    (.step (.dropLo 4 1787) <|
    .step (.xLo 1789) <|
    .splitBase 3 287
      (.step (.primeHi 3 283) <|
      .step (.dropLo 4 2281) <|
      .splitExp 0 8
        (.step (.grow 0 13) <|
        .missing 0 757)
        (.step (.dropLo 4 2543) <|
        .step (.xLo 2545) <|
        .splitExp 1 6
          (.step (.dropHi 4 2584) <|
          .step (.xHi 2581) <|
          .splitExp 0 10
            (.step (.grow 0 23) <|
            .step (.dropHi 4 2547) <|
            .step (.xLo 2553) <|
            .reject)
            (.step (.dropLo 4 2576) <|
            .step (.xLo 2577) <|
            .splitExp 2 4
              (.step (.dropHi 4 2579) <|
              .step (.xHi 2577) <|
              .missing 4 1289)
              (.step (.dropLo 4 2580) <|
              .step (.xLo 2581) <|
              .missing 4 1291)))
          (.step (.dropLo 4 2625) <|
          .splitExp 0 10
            (.step (.grow 0 23) <|
            .step (.dropHi 4 2633) <|
            .step (.xLo 2645) <|
            .reject)
            (.step (.dropLo 4 2660) <|
            .step (.xLo 2661) <|
            .splitExp 2 4
              (.step (.dropHi 4 2667) <|
              .step (.xHi 2665) <|
              .splitExp 0 12
                (.step (.dropHi 4 2663) <|
                .step (.xHi 2661) <|
                .missing 4 11)
                (.step (.dropLo 4 2664) <|
                .step (.xLo 2665) <|
                .missing 4 31))
              (.step (.dropLo 4 2665) <|
              .splitExp 0 12
                (.step (.dropHi 4 2668) <|
                .step (.xHi 2665) <|
                .missing 4 31)
                (.step (.dropLo 4 2669) <|
                .missing 4 89))))))
      (.step (.primeLo 3 293) <|
      .step (.dropHi 4 2019) <|
      .step (.xHi 2017) <|
      .splitExp 0 8
        (.step (.grow 0 13) <|
        .missing 0 757)
        (.step (.dropLo 4 1944) <|
        .step (.xLo 1945) <|
        .splitExp 1 6
          (.step (.dropHi 4 1968) <|
          .step (.xHi 1965) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 4 1964) <|
            .step (.xLo 1965) <|
            .missing 4 983))
          (.step (.dropLo 4 1992) <|
          .step (.xLo 1993) <|
          .splitExp 0 10
            (.step (.grow 0 23) <|
            .step (.dropHi 4 1996) <|
            .step (.xLo 2001) <|
            .reject)
            (.step (.dropLo 4 2012) <|
            .step (.xLo 2013) <|
            .splitExp 2 4
              (.step (.dropHi 4 2016) <|
              .step (.xHi 2013) <|
              .missing 4 19)
              (.step (.dropLo 4 2015) <|
              .step (.xLo 2017) <|
              .missing 4 1009))))))

theorem deficientFour5Part021 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,283,293,2,0⟩, ⟨true,1089,2669,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part021Tree [] _ _ (by decide +kernel)

private def deficientFour5Part022Tree : Tree :=
  .step (.primeLo 3 311) <|
  .step (.dropHi 4 1441) <|
  .splitExp 1 4
    (.step (.grow 1 11) <|
    .step (.grow 1 71) <|
    .step (.dropHi 4 986) <|
    .step (.xLo 781) <|
    .step (.xHi 781) <|
    .missing 4 23)
    (.step (.dropLo 4 827) <|
    .step (.xLo 829) <|
    .splitExp 2 2
      (.step (.grow 2 307) <|
      .step (.dropHi 4 1114) <|
      .step (.xLo 921) <|
      .step (.xHi 921) <|
      .missing 4 461)
      (.step (.dropLo 4 994) <|
      .step (.xLo 997) <|
      .splitBase 3 323
        (.step (.primeHi 3 317) <|
        .step (.dropLo 4 1221) <|
        .splitExp 0 8
          (.step (.grow 0 13) <|
          .missing 0 757)
          (.step (.dropLo 4 1293) <|
          .splitBase 3 313
            (.step (.dropLo 4 1364) <|
            .step (.xLo 1365) <|
            .splitBase 3 311
              (.step (.dropLo 4 1404) <|
              .step (.xLo 1405) <|
              .splitExp 1 6
                (.step (.dropHi 4 1415) <|
                .step (.xHi 1413) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.reject))
                (.step (.dropLo 4 1428) <|
                .step (.xLo 1429) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 4 1439) <|
                  .step (.xLo 1441) <|
                  .missing 4 7)))
              (.step (.primeLo 3 313) <|
              .step (.dropHi 4 1400) <|
              .step (.xHi 1397) <|
              .splitExp 1 6
                (.step (.dropHi 4 1375) <|
                .step (.xHi 1373) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.reject))
                (.step (.dropLo 4 1387) <|
                .step (.xLo 1389) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 4 1397) <|
                  .missing 4 233))))
            (.step (.primeLo 3 317) <|
            .step (.dropHi 4 1325) <|
            .splitExp 1 6
              (.step (.dropHi 4 1303) <|
              .step (.xHi 1301) <|
              .splitExp 0 10
                (.missing 0 23)
                (.step (.dropLo 4 1301) <|
                .missing 4 7))
              (.step (.dropLo 4 1314) <|
              .step (.xLo 1317) <|
              .splitExp 0 10
                (.missing 0 23)
                (.step (.dropLo 4 1322) <|
                .step (.xLo 1325) <|
                .missing 4 13)))))
        (.step (.primeLo 3 331) <|
        .step (.dropHi 4 1125) <|
        .splitExp 0 8
          (.step (.grow 0 13) <|
          .missing 0 757)
          (.step (.dropLo 4 1040) <|
          .step (.xLo 1041) <|
          .splitBase 3 333
            (.step (.primeHi 3 331) <|
            .step (.dropLo 4 1102) <|
            .step (.xLo 1105) <|
            .splitExp 1 6
              (.step (.dropHi 4 1109) <|
              .splitExp 0 10
                (.missing 0 23)
                (.step (.dropLo 4 1108) <|
                .step (.xLo 1109) <|
                .missing 4 37))
              (.step (.dropLo 4 1117) <|
              .splitExp 0 10
                (.missing 0 23)
                (.step (.dropLo 4 1124) <|
                .step (.xLo 1125) <|
                .missing 4 563)))
            (.step (.primeLo 3 337) <|
            .step (.dropHi 4 1060) <|
            .step (.xHi 1057) <|
            .splitExp 1 6
              (.step (.dropHi 4 1046) <|
              .step (.xHi 1045) <|
              .splitExp 0 10
                (.missing 0 23)
                (.reject))
              (.step (.dropLo 4 1054) <|
              .step (.xLo 1057) <|
              .missing 4 23))))))

theorem deficientFour5Part022 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,308,337,2,0⟩, ⟨true,661,2669,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part022Tree [] _ _ (by decide +kernel)

private def deficientFour5Part023Tree : Tree :=
  .step (.dropLo 4 748) <|
  .step (.xLo 749) <|
  .splitBase 3 361
    (.step (.primeHi 3 359) <|
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
          (.step (.dropHi 4 960) <|
          .step (.xHi 957) <|
          .splitBase 3 347
            (.step (.dropLo 4 955) <|
            .step (.xLo 957) <|
            .missing 4 479)
            (.step (.primeLo 3 349) <|
            .step (.dropHi 4 945) <|
            .splitExp 0 10
              (.missing 0 23)
              (.step (.dropLo 4 945) <|
              .missing 4 11)))
          (.step (.dropLo 4 951) <|
          .step (.xLo 953) <|
          .splitBase 3 347
            (.step (.dropLo 4 966) <|
            .step (.xLo 969) <|
            .missing 4 97)
            (.step (.primeLo 3 349) <|
            .step (.dropHi 4 956) <|
            .step (.xHi 953) <|
            .missing 4 53))))
      (.step (.primeLo 3 353) <|
      .step (.dropHi 4 927) <|
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
            (.step (.dropHi 4 917) <|
            .splitExp 0 10
              (.missing 0 23)
              (.step (.dropLo 4 916) <|
              .step (.xLo 917) <|
              .splitExp 2 4
                (.reject)
                (.splitExp 0 12
                  (.reject)
                  (.reject))))
            (.step (.dropLo 4 923) <|
            .step (.xLo 925) <|
            .missing 4 463))
          (.step (.primeLo 3 359) <|
          .step (.dropHi 4 888) <|
          .step (.xHi 885) <|
          .splitExp 1 6
            (.step (.dropHi 4 878) <|
            .step (.xHi 877) <|
            .missing 4 439)
            (.step (.dropLo 4 884) <|
            .step (.xLo 885) <|
            .missing 4 443)))))
    (.step (.primeLo 3 367) <|
    .step (.dropHi 4 843) <|
    .step (.xHi 841) <|
    .splitBase 3 371
      (.step (.primeHi 3 367) <|
      .step (.dropLo 4 800) <|
      .step (.xLo 801) <|
      .splitExp 0 8
        (.missing 0 13)
        (.step (.dropLo 4 830) <|
        .step (.xLo 833) <|
        .splitExp 1 6
          (.step (.dropHi 4 834) <|
          .step (.xHi 833) <|
          .missing 4 139)
          (.step (.dropLo 4 839) <|
          .step (.xLo 841) <|
          .missing 4 421)))
      (.step (.primeLo 3 373) <|
      .step (.dropHi 4 812) <|
      .step (.xHi 809) <|
      .splitExp 0 8
        (.step (.grow 0 13) <|
        .missing 0 757)
        (.step (.dropLo 4 775) <|
        .step (.xLo 777) <|
        .splitBase 3 375
          (.step (.primeHi 3 373) <|
          .step (.dropLo 4 801) <|
          .splitExp 1 6
            (.step (.dropHi 4 804) <|
            .step (.xHi 801) <|
            .missing 4 401)
            (.step (.dropLo 4 809) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject)))
          (.step (.primeLo 3 379) <|
          .step (.dropHi 4 785) <|
          .splitExp 1 6
            (.step (.dropHi 4 777) <|
            .missing 4 389)
            (.step (.dropLo 4 782) <|
            .step (.xLo 785) <|
            .missing 4 131)))))

theorem deficientFour5Part023 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,379,2,0⟩, ⟨true,653,969,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part023Tree [] _ _ (by decide +kernel)

private def deficientFour5Part024Tree : Tree :=
  .step (.primeLo 3 383) <|
  .step (.dropHi 4 769) <|
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
                (.step (.dropHi 4 761) <|
                .missing 4 127)
                (.step (.dropLo 4 765) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 4 768) <|
                  .step (.xLo 769) <|
                  .missing 4 7)))
              (.step (.primeLo 3 389) <|
              .step (.dropHi 4 745) <|
              .splitExp 1 6
                (.step (.dropHi 4 738) <|
                .step (.xHi 737) <|
                .missing 4 41)
                (.step (.dropLo 4 743) <|
                .step (.xLo 745) <|
                .missing 4 373))))
          (.step (.primeLo 3 397) <|
          .step (.dropHi 4 717) <|
          .splitExp 0 8
            (.step (.grow 0 13) <|
            .missing 0 757)
            (.step (.dropLo 4 696) <|
            .step (.xLo 697) <|
            .splitBase 3 397
              (.step (.dropLo 4 709) <|
              .splitExp 1 6
                (.step (.dropHi 4 711) <|
                .step (.xHi 709) <|
                .missing 4 71)
                (.step (.dropLo 4 715) <|
                .step (.xLo 717) <|
                .missing 4 359))
              (.step (.primeLo 3 401) <|
              .step (.dropHi 4 705) <|
              .splitExp 1 6
                (.step (.dropHi 4 698) <|
                .step (.xHi 697) <|
                .missing 4 349)
                (.step (.dropLo 4 702) <|
                .step (.xLo 705) <|
                .missing 4 353)))))
        (.step (.primeLo 3 409) <|
        .step (.dropHi 4 681) <|
        .splitBase 3 413
          (.step (.primeHi 3 409) <|
          .step (.dropLo 4 653) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 4 673) <|
            .splitExp 1 6
              (.step (.dropHi 4 675) <|
              .step (.xHi 673) <|
              .missing 4 337)
              (.step (.dropLo 4 679) <|
              .step (.xLo 681) <|
              .missing 4 11)))
          (.step (.primeLo 3 419) <|
          .step (.dropHi 4 655) <|
          .step (.xHi 653) <|
          .splitExp 0 8
            (.step (.grow 0 13) <|
            .missing 0 757)
            (.step (.dropLo 4 643) <|
            .step (.xLo 645) <|
            .splitExp 1 6
              (.step (.dropHi 4 650) <|
              .step (.xHi 649) <|
              .splitBase 3 419
                (.step (.dropLo 4 648) <|
                .step (.xLo 649) <|
                .missing 4 13)
                (.step (.primeLo 3 421) <|
                .step (.dropHi 4 645) <|
                .missing 4 19))
              (.step (.dropLo 4 648) <|
              .step (.xLo 649) <|
              .splitBase 3 419
                (.step (.dropLo 4 653) <|
                .missing 4 109)
                (.step (.primeLo 3 421) <|
                .step (.dropHi 4 650) <|
                .step (.xHi 649) <|
                .missing 4 13)))))))

theorem deficientFour5Part024 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,380,421,2,0⟩, ⟨true,477,969,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part024Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
