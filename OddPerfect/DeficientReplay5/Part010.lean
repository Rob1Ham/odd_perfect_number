module

public import OddPerfect.DeficientReplay5.Part009

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour5Part045Tree : Tree :=
  .step (.dropLo 4 70) <|
  .step (.xLo 73) <|
  .splitExp 1 2
    (.splitBase 2 25
      (.step (.primeHi 2 23) <|
      .step (.dropLo 3 31) <|
      .step (.dropLo 4 202) <|
      .step (.xLo 205) <|
      .splitExp 0 4
        (.step (.grow 0 11) <|
        .step (.xLo 209) <|
        .step (.dropHi 3 36) <|
        .step (.primeHi 3 31) <|
        .reject)
        (.step (.dropLo 3 35) <|
        .step (.dropLo 4 782) <|
        .step (.primeLo 3 37) <|
        .step (.xLo 785) <|
        .step (.grow 1 31) <|
        .step (.dropHi 4 1388) <|
        .step (.xLo 837) <|
        .step (.xHi 1333) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 1146) <|
          .step (.xLo 1209) <|
          .splitExp 2 2
            (.missing 2 7)
            (.step (.dropLo 4 1265) <|
            .step (.xLo 1333) <|
            .missing 4 29))))
      (.step (.primeLo 2 29) <|
      .step (.primeLo 3 31) <|
      .step (.dropHi 4 212) <|
      .step (.xHi 209) <|
      .splitExp 0 4
        (.step (.grow 0 11) <|
        .step (.fix 1 31 3) <|
        .step (.dropLo 4 113) <|
        .reject)
        (.step (.dropLo 4 94) <|
        .step (.xLo 97) <|
        .step (.fix 1 31 3) <|
        .step (.dropLo 4 192) <|
        .step (.xLo 193) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 208) <|
          .step (.xLo 209) <|
          .missing 4 7))))
    (.step (.dropLo 2 24) <|
    .step (.dropLo 4 153) <|
    .step (.primeLo 2 29) <|
    .step (.primeLo 3 31) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.dropHi 4 1279) <|
      .step (.xLo 165) <|
      .step (.xHi 1265) <|
      .step (.dropHi 3 36) <|
      .step (.primeHi 3 31) <|
      .step (.dropLo 4 851) <|
      .step (.xLo 869) <|
      .splitExp 1 4
        (.missing 1 71)
        (.step (.dropLo 4 1151) <|
        .step (.xLo 1177) <|
        .splitExp 2 2
          (.missing 2 13)
          (.step (.dropLo 4 1208) <|
          .step (.xLo 1221) <|
          .splitExp 3 2
            (.missing 3 331)
            (.step (.dropLo 4 1259) <|
            .step (.xLo 1265) <|
            .missing 4 211))))
      (.step (.dropLo 3 33) <|
      .step (.dropLo 4 346) <|
      .step (.primeLo 3 37) <|
      .step (.xLo 349) <|
      .step (.dropHi 4 487) <|
      .step (.xHi 485) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.step (.dropLo 4 403) <|
        .step (.xLo 405) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .missing 1 71)
          (.step (.dropLo 4 460) <|
          .step (.xLo 461) <|
          .splitExp 0 8
            (.step (.grow 0 13) <|
            .missing 0 757)
            (.step (.dropLo 4 470) <|
            .step (.xLo 473) <|
            .splitExp 2 2
              (.step (.grow 2 13) <|
              .missing 2 67)
              (.step (.dropLo 4 479) <|
              .step (.xLo 481) <|
              .splitExp 3 2
                (.missing 3 7)
                (.step (.dropLo 4 484) <|
                .step (.xLo 485) <|
                .splitExp 1 6
                  (.reject)
                  (.reject))))))))

theorem deficientFour5Part045 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,29,2,0⟩, ⟨false,29,37,2,0⟩, ⟨true,45,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part045Tree [] _ _ (by decide +kernel)

private def deficientFour5Part046Tree : Tree :=
  .step (.primeHi 2 23) <|
  .step (.dropLo 4 179) <|
  .step (.xLo 181) <|
  .splitBase 3 45
    (.step (.primeHi 3 43) <|
    .step (.dropLo 4 913) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .splitBase 3 41
        (.reject)
        (.step (.primeLo 3 43) <|
        .step (.dropHi 4 1470) <|
        .step (.xHi 1441) <|
        .splitExp 1 4
          (.missing 1 71)
          (.step (.dropLo 4 1270) <|
          .step (.xLo 1309) <|
          .splitExp 2 2
            (.step (.grow 2 7) <|
            .missing 2 79)
            (.step (.dropLo 4 1417) <|
            .step (.xLo 1441) <|
            .missing 4 7))))
      (.reject))
    (.step (.primeLo 3 47) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.dropHi 4 369) <|
      .step (.xLo 209) <|
      .step (.xHi 341) <|
      .step (.dropHi 3 51) <|
      .step (.primeHi 3 47) <|
      .step (.dropLo 4 321) <|
      .step (.xLo 341) <|
      .missing 4 19)
      (.step (.dropLo 3 48) <|
      .step (.dropLo 4 525) <|
      .step (.primeLo 3 53) <|
      .step (.dropHi 4 962) <|
      .step (.xHi 961) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.step (.dropLo 4 667) <|
        .step (.xLo 669) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .step (.grow 1 71) <|
          .step (.dropHi 4 735) <|
          .step (.xLo 781) <|
          .reject)
          (.step (.dropLo 4 840) <|
          .step (.xLo 841) <|
          .splitExp 2 2
            (.step (.grow 2 7) <|
            .missing 2 79)
            (.step (.dropLo 4 902) <|
            .step (.xLo 905) <|
            .splitExp 0 8
              (.step (.grow 0 13) <|
              .missing 0 757)
              (.step (.dropLo 4 940) <|
              .step (.xLo 941) <|
              .splitExp 1 6
                (.step (.dropHi 4 950) <|
                .step (.xHi 949) <|
                .splitExp 3 2
                  (.step (.grow 3 7) <|
                  .missing 3 409)
                  (.step (.dropLo 4 946) <|
                  .step (.xLo 949) <|
                  .missing 4 19))
                (.step (.dropLo 4 951) <|
                .step (.xLo 953) <|
                .splitExp 3 2
                  (.missing 3 7)
                  (.step (.dropLo 4 957) <|
                  .splitExp 0 10
                    (.step (.dropHi 4 957) <|
                    .missing 4 479)
                    (.reject)))))))))

theorem deficientFour5Part046 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,25,2,0⟩, ⟨false,41,53,2,0⟩, ⟨true,69,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part046Tree [] _ _ (by decide +kernel)

private def deficientFour5Part047Tree : Tree :=
  .step (.dropLo 4 44) <|
  .step (.xLo 45) <|
  .splitBase 3 37
    (.use 0)
    (.step (.primeLo 3 41) <|
    .splitExp 1 2
      (.step (.grow 1 31) <|
      .step (.dropHi 4 291) <|
      .step (.xLo 93) <|
      .step (.xHi 217) <|
      .step (.dropHi 2 27) <|
      .step (.primeHi 2 23) <|
      .splitBase 3 45
        (.step (.primeHi 3 43) <|
        .step (.dropLo 4 114) <|
        .step (.xLo 217) <|
        .missing 4 109)
        (.step (.primeLo 3 47) <|
        .step (.dropHi 4 150) <|
        .step (.xHi 93) <|
        .step (.fix 4 47 3) <|
        .splitExp 0 4
          (.missing 0 11)
          (.reject)))
      (.step (.dropLo 4 67) <|
      .step (.xLo 69) <|
      .splitBase 2 25
        (.use 1)
        (.step (.primeLo 2 29) <|
        .step (.dropHi 4 209) <|
        .splitBase 3 45
          (.step (.primeHi 3 43) <|
          .step (.dropLo 4 96) <|
          .step (.xLo 97) <|
          .splitExp 0 4
            (.step (.grow 0 11) <|
            .step (.dropHi 4 112) <|
            .step (.xLo 121) <|
            .reject)
            (.step (.dropLo 4 148) <|
            .step (.xLo 149) <|
            .splitBase 3 41
              (.step (.dropLo 4 179) <|
              .step (.xLo 181) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 4 193) <|
                .splitExp 1 4
                  (.step (.grow 1 11) <|
                  .missing 1 71)
                  (.step (.dropLo 4 205) <|
                  .splitExp 0 8
                    (.missing 0 13)
                    (.step (.dropLo 4 207) <|
                    .step (.xLo 209) <|
                    .missing 4 7))))
              (.step (.primeLo 3 43) <|
              .step (.dropHi 4 168) <|
              .step (.xHi 165) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 4 158) <|
                .step (.xLo 161) <|
                .splitExp 1 4
                  (.step (.grow 1 11) <|
                  .missing 1 71)
                  (.reject)))))
          (.step (.primeLo 3 47) <|
          .step (.dropHi 4 125) <|
          .splitExp 0 4
            (.step (.grow 0 11) <|
            .step (.dropHi 3 52) <|
            .step (.dropHi 4 82) <|
            .step (.primeHi 3 47) <|
            .step (.xLo 77) <|
            .step (.xHi 77) <|
            .missing 4 13)
            (.step (.dropLo 4 89) <|
            .splitBase 3 49
              (.step (.primeHi 3 47) <|
              .step (.dropLo 4 114) <|
              .step (.xLo 117) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 4 120) <|
                .step (.xLo 121) <|
                .splitExp 1 4
                  (.step (.grow 1 11) <|
                  .missing 1 71)
                  (.step (.dropLo 4 124) <|
                  .step (.xLo 125) <|
                  .missing 4 7)))
              (.step (.primeLo 3 53) <|
              .step (.dropHi 4 95) <|
              .step (.xHi 93) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 4 92) <|
                .step (.xLo 93) <|
                .missing 4 47)))))))

private def deficientFour5Part047Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,29,2,0⟩, ⟨false,29,37,2,0⟩, ⟨true,45,0,1,1⟩], 1, deficientFour5Part045⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,25,2,0⟩, ⟨false,41,53,2,0⟩, ⟨true,69,0,1,1⟩], 1, deficientFour5Part046⟩]

theorem deficientFour5Part047 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,29,2,0⟩, ⟨false,29,53,2,0⟩, ⟨true,29,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part047Tree deficientFour5Part047Refs _ _ (by decide +kernel)

private def deficientFour5Part048Tree : Tree :=
  .step (.primeHi 2 31) <|
  .step (.dropLo 4 58) <|
  .step (.xLo 61) <|
  .splitBase 3 43
    (.step (.dropLo 4 79) <|
    .step (.xLo 81) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.dropHi 3 42) <|
      .step (.dropHi 4 117) <|
      .step (.primeHi 3 41) <|
      .step (.xLo 121) <|
      .reject)
      (.step (.dropLo 4 111) <|
      .step (.xLo 113) <|
      .splitBase 3 39
        (.step (.primeHi 3 37) <|
        .step (.dropLo 4 193) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 209) <|
          .splitExp 1 4
            (.step (.grow 1 11) <|
            .missing 1 71)
            (.step (.dropLo 4 224) <|
            .step (.xLo 225) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 4 226) <|
              .step (.xLo 229) <|
              .missing 4 23))))
        (.step (.primeLo 3 41) <|
        .step (.dropHi 4 141) <|
        .splitBase 3 41
          (.step (.dropLo 4 127) <|
          .step (.xLo 129) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 134) <|
            .step (.xLo 137) <|
            .splitExp 1 4
              (.missing 1 11)
              (.step (.dropLo 4 140) <|
              .step (.xLo 141) <|
              .missing 4 71)))
          (.step (.primeLo 3 43) <|
          .step (.dropHi 4 121) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 116) <|
            .step (.xLo 117) <|
            .splitExp 1 4
              (.step (.grow 1 11) <|
              .missing 1 71)
              (.step (.dropLo 4 120) <|
              .step (.xLo 121) <|
              .missing 4 61))))))
    (.step (.primeLo 3 47) <|
    .step (.dropHi 4 97) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.dropHi 3 51) <|
      .step (.dropHi 4 69) <|
      .step (.primeHi 3 47) <|
      .step (.xLo 77) <|
      .reject)
      (.step (.dropLo 4 74) <|
      .step (.xLo 77) <|
      .splitBase 3 49
        (.step (.primeHi 3 47) <|
        .step (.dropLo 4 90) <|
        .step (.xLo 93) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 94) <|
          .step (.xLo 97) <|
          .missing 4 7))
        (.step (.primeLo 3 53) <|
        .step (.dropHi 4 78) <|
        .step (.xHi 77) <|
        .missing 4 13)))

theorem deficientFour5Part048 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,31,35,2,0⟩, ⟨false,37,53,2,0⟩, ⟨true,41,229,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part048Tree [] _ _ (by decide +kernel)

private def deficientFour5Part049Tree : Tree :=
  .step (.dropLo 4 38) <|
  .step (.xLo 41) <|
  .splitBase 2 35
    (.use 0)
    (.step (.primeLo 2 37) <|
    .step (.primeLo 3 41) <|
    .step (.dropHi 4 79) <|
    .step (.xHi 77) <|
    .splitBase 3 45
      (.step (.primeHi 3 43) <|
      .step (.primeHi 2 41) <|
      .step (.dropLo 4 48) <|
      .step (.xLo 49) <|
      .splitExp 0 4
        (.step (.grow 0 11) <|
        .step (.dropHi 4 59) <|
        .step (.xLo 77) <|
        .reject)
        (.step (.dropLo 4 58) <|
        .step (.xLo 61) <|
        .splitBase 2 37
          (.step (.dropLo 4 69) <|
          .splitBase 3 41
            (.step (.dropLo 4 75) <|
            .step (.xLo 77) <|
            .missing 4 13)
            (.step (.primeLo 3 43) <|
            .step (.dropHi 4 72) <|
            .step (.xHi 69) <|
            .missing 4 7))
          (.step (.primeLo 2 41) <|
          .step (.primeLo 3 43) <|
          .reject)))
      (.step (.primeLo 3 47) <|
      .step (.dropHi 4 63) <|
      .step (.xHi 61) <|
      .splitExp 0 4
        (.missing 0 11)
        (.step (.dropLo 4 44) <|
        .step (.xLo 45) <|
        .splitBase 2 39
          (.step (.primeHi 2 37) <|
          .step (.dropLo 4 53) <|
          .splitBase 3 49
            (.step (.primeHi 3 47) <|
            .step (.dropLo 4 61) <|
            .missing 4 31)
            (.step (.primeLo 3 53) <|
            .step (.dropHi 4 54) <|
            .step (.xHi 53) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.reject)))
          (.step (.primeLo 2 41) <|
          .step (.dropHi 4 54) <|
          .step (.xHi 53) <|
          .splitBase 3 49
            (.step (.primeHi 3 47) <|
            .step (.dropLo 4 49) <|
            .splitBase 2 41
              (.step (.dropLo 4 52) <|
              .step (.xLo 53) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.splitExp 1 4
                  (.missing 1 11)
                  (.reject)))
              (.step (.primeLo 2 43) <|
              .step (.dropHi 4 50) <|
              .step (.xHi 49) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.reject)))
            (.step (.primeLo 3 53) <|
            .step (.dropHi 4 47) <|
            .step (.xHi 45) <|
            .missing 4 23)))))

private def deficientFour5Part049Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,31,35,2,0⟩, ⟨false,37,53,2,0⟩, ⟨true,41,229,1,1⟩], 1, deficientFour5Part048⟩]

theorem deficientFour5Part049 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,31,43,2,0⟩, ⟨false,37,53,2,0⟩, ⟨true,29,229,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part049Tree deficientFour5Part049Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
