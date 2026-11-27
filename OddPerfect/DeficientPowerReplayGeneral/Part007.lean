module

public import OddPerfect.DeficientPowerReplayGeneral.Part006

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart030Tree : Tree :=
  .step (.primeHi 3 271) <|
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
        (.step (.dropHi 4 4943) <|
        .step (.xHi 4941) <|
        .splitExp 0 10
          (.step (.grow 0 23) <|
          .step (.dropHi 4 4809) <|
          .step (.xLo 4853) <|
          .reject)
          (.step (.dropLo 4 4910) <|
          .step (.xLo 4913) <|
          .splitExp 2 4
            (.step (.dropHi 4 4926) <|
            .step (.xHi 4925) <|
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
          .step (.dropHi 4 5124) <|
          .step (.xLo 5129) <|
          .reject)
          (.step (.dropLo 4 5225) <|
          .splitExp 2 4
            (.step (.dropHi 4 5257) <|
            .splitExp 0 12
              (.step (.dropHi 4 5240) <|
              .step (.xHi 5237) <|
              .splitExp 1 8
                (.step (.grow 1 19) <|
                .missing 1 31)
                (.reject))
              (.step (.dropLo 4 5240) <|
              .step (.xLo 5241) <|
              .splitExp 1 8
                (.missing 1 19)
                (.step (.dropLo 4 5254) <|
                .step (.xLo 5257) <|
                .missing 4 11)))
            (.step (.dropLo 4 5244) <|
            .step (.xLo 5245) <|
            .splitExp 0 12
              (.step (.dropHi 4 5260) <|
              .step (.xHi 5257) <|
              .splitExp 1 8
                (.missing 1 19)
                (.reject))
              (.step (.dropLo 4 5259) <|
              .step (.xLo 5261) <|
              .splitExp 1 8
                (.missing 1 19)
                (.step (.dropLo 4 5273) <|
                .splitExp 0 14
                  (.missing 0 11)
                  (.step (.dropLo 4 5275) <|
                  .step (.xLo 5277) <|
                  .missing 4 7)))))))
      (.use 0))

private def deficientFourPowerGeneralPart030Refs : List Known := [
  ⟨#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,270,271,2,0⟩, ⟨true,4233,5277,5,0⟩], 1, deficientFourPowerGeneralPart029⟩]

theorem deficientFourPowerGeneralPart030 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,273,2,0⟩, ⟨true,2421,5277,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart030Tree deficientFourPowerGeneralPart030Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart031Tree : Tree :=
  .step (.dropLo 4 3160) <|
  .step (.xLo 3161) <|
  .splitExp 1 6
    (.step (.dropHi 4 3225) <|
    .splitExp 0 10
      (.step (.grow 0 23) <|
      .step (.dropHi 4 3168) <|
      .step (.xLo 3197) <|
      .reject)
      (.step (.dropLo 4 3211) <|
      .step (.xLo 3213) <|
      .splitExp 2 4
        (.step (.dropHi 4 3218) <|
        .step (.xHi 3217) <|
        .splitExp 0 12
          (.reject)
          (.reject))
        (.step (.dropLo 4 3218) <|
        .step (.xLo 3221) <|
        .splitExp 0 12
          (.reject)
          (.step (.dropLo 4 3224) <|
          .step (.xLo 3225) <|
          .missing 4 1613))))
    (.step (.dropLo 4 3288) <|
    .step (.xLo 3289) <|
    .splitExp 0 10
      (.step (.grow 0 23) <|
      .step (.dropHi 4 3301) <|
      .step (.xHi 3289) <|
      .missing 4 7)
      (.step (.dropLo 4 3343) <|
      .step (.xLo 3345) <|
      .splitExp 2 4
        (.step (.dropHi 4 3356) <|
        .step (.xHi 3353) <|
        .splitExp 0 12
          (.step (.dropHi 4 3349) <|
          .splitExp 1 8
            (.missing 1 19)
            (.step (.dropLo 4 3348) <|
            .step (.xLo 3349) <|
            .missing 4 67))
          (.step (.dropLo 4 3349) <|
          .splitExp 1 8
            (.missing 1 19)
            (.reject)))
        (.step (.dropLo 4 3351) <|
        .step (.xLo 3353) <|
        .splitExp 0 12
          (.step (.dropHi 4 3357) <|
          .splitExp 1 8
            (.missing 1 19)
            (.step (.dropLo 4 3356) <|
            .step (.xLo 3357) <|
            .missing 4 23))
          (.step (.dropLo 4 3357) <|
          .splitExp 1 8
            (.missing 1 19)
            (.reject)))))

theorem deficientFourPowerGeneralPart031 : Closed (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,2717,3361,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart031Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart032Tree : Tree :=
  .step (.dropLo 4 752) <|
  .step (.xLo 753) <|
  .splitBase 3 241
    (.use 0)
    (.step (.primeLo 3 251) <|
    .splitExp 0 6
      (.step (.grow 0 1093) <|
      .step (.dropHi 4 2637) <|
      .step (.xLo 1093) <|
      .step (.xHi 1093) <|
      .missing 4 547)
      (.step (.dropLo 4 1083) <|
      .step (.xLo 1085) <|
      .splitBase 3 265
        (.use 1)
        (.step (.primeLo 3 269) <|
        .step (.dropHi 4 5277) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .step (.grow 1 71) <|
          .step (.dropHi 4 1963) <|
          .step (.xLo 3905) <|
          .reject)
          (.step (.dropLo 4 1623) <|
          .step (.xLo 1625) <|
          .splitExp 2 2
            (.step (.grow 2 307) <|
            .step (.dropHi 4 2544) <|
            .step (.xLo 2149) <|
            .step (.xHi 2149) <|
            .missing 4 43)
            (.step (.dropLo 4 2420) <|
            .step (.xLo 2421) <|
            .splitBase 3 273
              (.use 2)
              (.step (.primeLo 3 277) <|
              .step (.dropHi 4 3364) <|
              .step (.xHi 3361) <|
              .splitExp 0 8
                (.step (.grow 0 13) <|
                .missing 0 757)
                (.step (.dropLo 4 2717) <|
                .splitBase 3 277
                  (.use 3)
                  (.step (.primeLo 3 281) <|
                  .step (.dropHi 4 2867) <|
                  .step (.xHi 2865) <|
                  .splitExp 1 6
                    (.step (.dropHi 4 2765) <|
                    .splitExp 0 10
                      (.step (.grow 0 23) <|
                      .step (.dropHi 4 2723) <|
                      .step (.xLo 2737) <|
                      .reject)
                      (.step (.dropLo 4 2755) <|
                      .step (.xLo 2757) <|
                      .splitExp 2 4
                        (.step (.dropHi 4 2760) <|
                        .step (.xHi 2757) <|
                        .missing 4 7)
                        (.step (.dropLo 4 2760) <|
                        .step (.xLo 2761) <|
                        .splitExp 0 12
                          (.reject)
                          (.step (.dropLo 4 2764) <|
                          .step (.xLo 2765) <|
                          .missing 4 461))))
                    (.step (.dropLo 4 2811) <|
                    .step (.xLo 2813) <|
                    .splitExp 0 10
                      (.step (.grow 0 23) <|
                      .step (.dropHi 4 2821) <|
                      .step (.xLo 2829) <|
                      .reject)
                      (.step (.dropLo 4 2851) <|
                      .step (.xLo 2853) <|
                      .splitExp 2 4
                        (.step (.dropHi 4 2861) <|
                        .splitExp 0 12
                          (.step (.dropHi 4 2856) <|
                          .step (.xHi 2853) <|
                          .missing 4 1427)
                          (.step (.dropLo 4 2856) <|
                          .step (.xLo 2857) <|
                          .splitExp 1 8
                            (.missing 1 19)
                            (.step (.dropLo 4 2860) <|
                            .step (.xLo 2861) <|
                            .missing 4 53)))
                        (.step (.dropLo 4 2857) <|
                        .splitExp 0 12
                          (.step (.dropHi 4 2862) <|
                          .step (.xHi 2861) <|
                          .splitExp 1 8
                            (.missing 1 19)
                            (.reject))
                          (.step (.dropLo 4 2862) <|
                          .step (.xLo 2865) <|
                          .missing 4 1433))))))))))))

private def deficientFourPowerGeneralPart032Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,211,241,2,0⟩, ⟨true,753,0,5,0⟩], 1, deficientFourPowerGeneralPart023⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,251,265,2,0⟩, ⟨true,1085,0,5,0⟩], 1, deficientFourPowerGeneralPart028⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,273,2,0⟩, ⟨true,2421,5277,5,0⟩], 1, deficientFourPowerGeneralPart030⟩,
  ⟨#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,2717,3361,5,0⟩], 1, deficientFourPowerGeneralPart031⟩]

theorem deficientFourPowerGeneralPart032 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,211,281,2,0⟩, ⟨true,397,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart032Tree deficientFourPowerGeneralPart032Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart033Tree : Tree :=
  .step (.dropLo 4 1312) <|
  .step (.xLo 1313) <|
  .splitExp 2 2
    (.step (.grow 2 307) <|
    .step (.dropHi 4 1731) <|
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
          (.step (.dropHi 4 2585) <|
          .splitExp 0 10
            (.step (.grow 0 23) <|
            .step (.dropHi 4 2548) <|
            .step (.xLo 2553) <|
            .reject)
            (.step (.dropLo 4 2576) <|
            .step (.xLo 2577) <|
            .splitExp 2 4
              (.step (.dropHi 4 2580) <|
              .step (.xHi 2577) <|
              .missing 4 1289)
              (.step (.dropLo 4 2580) <|
              .step (.xLo 2581) <|
              .splitExp 0 12
                (.step (.dropHi 4 2581) <|
                .missing 4 1291)
                (.step (.dropLo 4 2584) <|
                .step (.xLo 2585) <|
                .missing 4 431))))
          (.step (.dropLo 4 2625) <|
          .splitExp 0 10
            (.step (.grow 0 23) <|
            .step (.dropHi 4 2634) <|
            .step (.xLo 2645) <|
            .reject)
            (.step (.dropLo 4 2660) <|
            .step (.xLo 2661) <|
            .splitExp 2 4
              (.step (.dropHi 4 2668) <|
              .step (.xHi 2665) <|
              .splitExp 0 12
                (.step (.dropHi 4 2664) <|
                .step (.xHi 2661) <|
                .missing 4 11)
                (.step (.dropLo 4 2664) <|
                .step (.xLo 2665) <|
                .missing 4 31))
              (.step (.dropLo 4 2665) <|
              .splitExp 0 12
                (.step (.dropHi 4 2669) <|
                .splitExp 1 8
                  (.missing 1 19)
                  (.step (.dropLo 4 2668) <|
                  .step (.xLo 2669) <|
                  .missing 4 89))
                (.step (.dropLo 4 2669) <|
                .splitExp 1 8
                  (.missing 1 19)
                  (.step (.dropLo 4 2672) <|
                  .step (.xLo 2673) <|
                  .missing 4 7)))))))
      (.step (.primeLo 3 293) <|
      .step (.dropHi 4 2020) <|
      .step (.xHi 2017) <|
      .splitExp 0 8
        (.step (.grow 0 13) <|
        .missing 0 757)
        (.step (.dropLo 4 1944) <|
        .step (.xLo 1945) <|
        .splitExp 1 6
          (.step (.dropHi 4 1969) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 4 1964) <|
            .step (.xLo 1965) <|
            .splitExp 2 4
              (.step (.dropHi 4 1966) <|
              .step (.xHi 1965) <|
              .missing 4 983)
              (.step (.dropLo 4 1966) <|
              .step (.xLo 1969) <|
              .missing 4 197)))
          (.step (.dropLo 4 1992) <|
          .step (.xLo 1993) <|
          .splitExp 0 10
            (.step (.grow 0 23) <|
            .step (.dropHi 4 1997) <|
            .step (.xLo 2001) <|
            .reject)
            (.step (.dropLo 4 2012) <|
            .step (.xLo 2013) <|
            .splitExp 2 4
              (.splitExp 0 12
                (.step (.dropHi 4 2014) <|
                .step (.xHi 2013) <|
                .missing 4 19)
                (.step (.dropLo 4 2014) <|
                .step (.xLo 2017) <|
                .missing 4 1009))
              (.step (.dropLo 4 2015) <|
              .step (.xLo 2017) <|
              .missing 4 1009))))))

theorem deficientFourPowerGeneralPart033 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,283,293,2,0⟩, ⟨true,1089,2673,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart033Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart034Tree : Tree :=
  .step (.dropLo 4 994) <|
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
            (.step (.dropHi 4 1416) <|
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
          .step (.dropHi 4 1401) <|
          .splitExp 1 6
            (.step (.dropHi 4 1376) <|
            .step (.xHi 1373) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject))
            (.step (.dropLo 4 1387) <|
            .step (.xLo 1389) <|
            .splitExp 0 10
              (.missing 0 23)
              (.step (.dropLo 4 1397) <|
              .splitExp 2 4
                (.step (.dropHi 4 1399) <|
                .step (.xHi 1397) <|
                .missing 4 233)
                (.step (.dropLo 4 1398) <|
                .step (.xLo 1401) <|
                .missing 4 701)))))
        (.step (.primeLo 3 317) <|
        .step (.dropHi 4 1326) <|
        .step (.xHi 1325) <|
        .splitExp 1 6
          (.step (.dropHi 4 1304) <|
          .step (.xHi 1301) <|
          .splitExp 0 10
            (.missing 0 23)
            (.reject))
          (.step (.dropLo 4 1314) <|
          .step (.xLo 1317) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 4 1322) <|
            .step (.xLo 1325) <|
            .missing 4 13)))))
    (.step (.primeLo 3 331) <|
    .step (.dropHi 4 1126) <|
    .step (.xHi 1125) <|
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
          (.step (.dropHi 4 1110) <|
          .step (.xHi 1109) <|
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
        .step (.dropHi 4 1061) <|
        .splitExp 1 6
          (.step (.dropHi 4 1047) <|
          .step (.xHi 1045) <|
          .splitExp 0 10
            (.missing 0 23)
            (.reject))
          (.step (.dropLo 4 1054) <|
          .step (.xLo 1057) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 4 1059) <|
            .step (.xLo 1061) <|
            .missing 4 59)))))

theorem deficientFourPowerGeneralPart034 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,311,337,2,0⟩, ⟨true,829,1441,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart034Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
