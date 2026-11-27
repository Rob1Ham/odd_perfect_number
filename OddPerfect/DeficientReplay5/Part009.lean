module

public import OddPerfect.DeficientReplay5.Part008

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour5Part040Tree : Tree :=
  .step (.primeHi 3 787) <|
  .step (.dropLo 4 99) <|
  .step (.xLo 101) <|
  .splitBase 3 527
    (.step (.primeHi 3 523) <|
    .step (.dropLo 4 105) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 4 110) <|
      .step (.xLo 113) <|
      .splitBase 3 451
        (.step (.primeHi 3 449) <|
        .step (.dropLo 4 114) <|
        .step (.xLo 117) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .missing 1 71)
          (.step (.dropLo 4 118) <|
          .step (.xLo 121) <|
          .step (.dropHi 3 446) <|
          .step (.primeHi 3 443) <|
          .splitBase 3 417
            (.step (.primeHi 3 409) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 124) <|
              .step (.xLo 125) <|
              .missing 4 7))
            (.step (.primeLo 3 419) <|
            .step (.dropHi 4 123) <|
            .step (.xHi 121) <|
            .missing 4 61)))
        (.step (.primeLo 3 457) <|
        .step (.dropHi 4 120) <|
        .step (.xHi 117) <|
        .splitExp 1 4
          (.missing 1 11)
          (.step (.dropLo 3 461) <|
          .step (.dropLo 4 114) <|
          .step (.xLo 117) <|
          .missing 4 59))))
    (.step (.primeLo 3 541) <|
    .step (.dropHi 4 115) <|
    .step (.xHi 113) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 4 103) <|
      .step (.xLo 105) <|
      .splitBase 3 641
        (.step (.dropLo 4 106) <|
        .step (.xLo 109) <|
        .splitExp 1 4
          (.missing 1 11)
          (.step (.dropLo 4 110) <|
          .step (.xLo 113) <|
          .step (.dropHi 3 602) <|
          .step (.primeHi 3 601) <|
          .splitExp 2 2
            (.missing 2 127)
            (.step (.dropLo 3 580) <|
            .step (.primeLo 3 587) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 595) <|
              .step (.primeLo 3 599) <|
              .splitExp 1 6
                (.reject)
                (.step (.dropLo 3 600) <|
                .step (.primeLo 3 601) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.reject))))))
        (.step (.primeLo 3 643) <|
        .step (.dropHi 4 111) <|
        .step (.xHi 109) <|
        .splitExp 1 4
          (.missing 1 11)
          (.step (.dropLo 3 646) <|
          .step (.dropLo 4 106) <|
          .step (.primeLo 3 647) <|
          .step (.xLo 109) <|
          .missing 4 11))))

theorem deficientFour5Part040 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,397,793,2,0⟩, ⟨true,89,125,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part040Tree [] _ _ (by decide +kernel)

private def deficientFour5Part041Tree : Tree :=
  .step (.primeLo 3 197) <|
  .splitBase 2 17
    (.use 0)
    (.step (.primeLo 2 19) <|
    .step (.dropHi 4 185) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.dropHi 3 4848) <|
      .step (.dropHi 4 104) <|
      .step (.primeHi 3 4831) <|
      .step (.xLo 77) <|
      .step (.xHi 77) <|
      .missing 4 13)
      (.step (.dropLo 4 88) <|
      .step (.xLo 89) <|
      .splitBase 3 393
        (.use 1)
        (.step (.primeLo 3 397) <|
        .step (.dropHi 4 125) <|
        .splitBase 3 793
          (.use 2)
          (.step (.primeLo 3 797) <|
          .step (.dropHi 4 108) <|
          .step (.xHi 105) <|
          .splitBase 3 1593
            (.step (.primeHi 3 1583) <|
            .step (.dropLo 4 93) <|
            .splitBase 3 1059
              (.step (.primeHi 3 1051) <|
              .step (.dropLo 4 96) <|
              .step (.xLo 97) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 4 100) <|
                .step (.xLo 101) <|
                .splitExp 1 4
                  (.missing 1 11)
                  (.step (.dropLo 3 832) <|
                  .step (.dropLo 4 103) <|
                  .step (.primeLo 3 839) <|
                  .step (.xLo 105) <|
                  .missing 4 53)))
              (.step (.primeLo 3 1061) <|
              .step (.dropHi 4 104) <|
              .step (.xHi 101) <|
              .splitExp 0 6
                (.step (.fix 0 1093 3) <|
                .step (.dropLo 4 95) <|
                .step (.dropHi 4 99) <|
                .step (.xLo 97) <|
                .step (.xHi 97) <|
                .missing 4 7)
                (.step (.dropLo 4 97) <|
                .splitExp 1 4
                  (.missing 1 11)
                  (.step (.dropLo 3 1207) <|
                  .step (.dropLo 4 100) <|
                  .step (.primeLo 3 1213) <|
                  .step (.xLo 101) <|
                  .missing 4 17))))
            (.step (.primeLo 3 1597) <|
            .step (.dropHi 4 101) <|
            .splitBase 3 3193
              (.step (.primeHi 3 3191) <|
              .step (.dropLo 4 90) <|
              .step (.xLo 93) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 4 94) <|
                .step (.xLo 97) <|
                .splitExp 1 4
                  (.missing 1 11)
                  (.splitBase 3 2127
                    (.step (.primeHi 3 2113) <|
                    .step (.dropLo 4 98) <|
                    .step (.xLo 101) <|
                    .missing 4 17)
                    (.step (.primeLo 3 2129) <|
                    .step (.dropHi 4 99) <|
                    .step (.xHi 97) <|
                    .missing 4 7))))
              (.step (.primeLo 3 3203) <|
              .step (.dropHi 4 97) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 4 91) <|
                .step (.xLo 93) <|
                .splitExp 1 4
                  (.missing 1 11)
                  (.step (.dropLo 4 94) <|
                  .step (.xLo 97) <|
                  .missing 4 7))))))))

private def deficientFour5Part041Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,197,0,2,0⟩, ⟨true,69,0,1,1⟩], 1, deficientFour5Part037⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,197,393,2,0⟩, ⟨true,89,185,1,1⟩], 1, deficientFour5Part039⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,397,793,2,0⟩, ⟨true,89,125,1,1⟩], 1, deficientFour5Part040⟩]

theorem deficientFour5Part041 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,194,0,2,0⟩, ⟨true,69,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part041Tree deficientFour5Part041Refs _ _ (by decide +kernel)

private def deficientFour5Part042Tree : Tree :=
  .step (.primeLo 3 97) <|
  .splitExp 1 2
    (.step (.grow 1 31) <|
    .step (.dropHi 4 631) <|
    .step (.xLo 93) <|
    .step (.xHi 589) <|
    .step (.dropHi 3 800) <|
    .step (.primeHi 3 797) <|
    .splitBase 3 171
      (.step (.primeHi 3 167) <|
      .splitBase 2 17
        (.step (.dropLo 4 97) <|
        .step (.xLo 217) <|
        .step (.dropHi 3 136) <|
        .step (.primeHi 3 131) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .reject)
          (.splitBase 3 111
            (.step (.primeHi 3 109) <|
            .step (.dropLo 4 295) <|
            .step (.xLo 341) <|
            .splitBase 3 101
              (.step (.dropLo 4 376) <|
              .step (.xLo 465) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.splitBase 3 97
                  (.step (.dropLo 4 544) <|
                  .step (.xLo 589) <|
                  .missing 4 59)
                  (.step (.primeLo 3 101) <|
                  .step (.dropHi 4 500) <|
                  .step (.xHi 465) <|
                  .missing 4 233)))
              (.step (.primeLo 3 103) <|
              .step (.dropHi 4 456) <|
              .step (.xHi 341) <|
              .missing 4 19))
            (.step (.primeLo 3 113) <|
            .step (.dropHi 4 326) <|
            .step (.xHi 217) <|
            .missing 4 109)))
        (.step (.primeLo 2 19) <|
        .step (.dropHi 3 128) <|
        .step (.dropHi 4 122) <|
        .step (.primeHi 3 127) <|
        .step (.xHi 93) <|
        .missing 4 47))
      (.step (.primeLo 3 173) <|
      .step (.dropHi 2 18) <|
      .step (.dropHi 4 162) <|
      .step (.primeHi 2 17) <|
      .step (.xHi 93) <|
      .missing 4 47))
    (.step (.dropLo 4 66) <|
    .step (.xLo 69) <|
    .splitBase 3 193
      (.step (.dropLo 4 101) <|
      .splitBase 2 17
        (.step (.dropLo 3 117) <|
        .step (.dropLo 4 297) <|
        .step (.primeLo 3 127) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 7550) <|
          .step (.xHi 7513) <|
          .splitBase 3 153
            (.use 0)
            (.step (.primeLo 3 157) <|
            .step (.dropHi 4 606) <|
            .step (.xHi 605) <|
            .splitBase 3 173
              (.step (.dropLo 4 362) <|
              .step (.xLo 385) <|
              .splitBase 3 163
                (.step (.dropLo 4 415) <|
                .step (.xLo 429) <|
                .splitExp 1 4
                  (.missing 1 71)
                  (.step (.dropLo 4 476) <|
                  .step (.xLo 517) <|
                  .splitExp 2 2
                    (.missing 2 307)
                    (.step (.dropLo 4 527) <|
                    .step (.xLo 561) <|
                    .step (.dropHi 3 160) <|
                    .step (.primeHi 3 157) <|
                    .step (.dropLo 4 602) <|
                    .step (.xLo 605) <|
                    .missing 4 101)))
                (.step (.primeLo 3 167) <|
                .step (.dropHi 4 491) <|
                .step (.xHi 473) <|
                .splitExp 1 4
                  (.missing 1 71)
                  (.step (.dropLo 4 407) <|
                  .step (.xLo 429) <|
                  .splitExp 2 2
                    (.missing 2 307)
                    (.step (.dropLo 3 168) <|
                    .step (.dropLo 4 444) <|
                    .step (.primeLo 3 173) <|
                    .step (.xLo 473) <|
                    .missing 4 79))))
              (.step (.primeLo 3 179) <|
              .step (.dropHi 4 410) <|
              .step (.xHi 385) <|
              .splitExp 1 4
                (.missing 1 71)
                (.step (.dropLo 4 327) <|
                .step (.xLo 341) <|
                .splitBase 3 185
                  (.step (.primeHi 3 181) <|
                  .step (.dropLo 4 368) <|
                  .step (.xLo 385) <|
                  .missing 4 193)
                  (.step (.primeLo 3 191) <|
                  .step (.dropHi 4 358) <|
                  .step (.xHi 341) <|
                  .missing 4 19)))))
          (.reject))
        (.use 1))
      (.use 2))

private def deficientFour5Part042Refs : List Known := [
  ⟨#v[⟨false,3,3,4,4⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,127,153,2,0⟩, ⟨true,297,7513,1,1⟩], 11, deficientFour5Part006⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,18,19,2,0⟩, ⟨false,97,193,2,0⟩, ⟨true,101,0,1,1⟩], 1, deficientFour5Part012⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,194,0,2,0⟩, ⟨true,69,0,1,1⟩], 1, deficientFour5Part041⟩]

theorem deficientFour5Part042 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,19,2,0⟩, ⟨false,94,0,2,0⟩, ⟨true,45,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part042Tree deficientFour5Part042Refs _ _ (by decide +kernel)

private def deficientFour5Part043Tree : Tree :=
  .step (.dropLo 2 13) <|
  .step (.dropLo 3 44) <|
  .step (.dropLo 4 44) <|
  .step (.primeLo 3 47) <|
  .step (.xLo 45) <|
  .splitBase 2 15
    (.step (.primeHi 2 13) <|
    .reject)
    (.step (.primeLo 2 17) <|
    .splitBase 3 93
      (.step (.primeHi 3 89) <|
      .step (.dropLo 4 87) <|
      .step (.xLo 89) <|
      .splitExp 1 2
        (.step (.grow 1 31) <|
        .step (.xLo 93) <|
        .splitBase 3 61
          (.step (.dropLo 4 160) <|
          .step (.xLo 217) <|
          .splitBase 2 17
            (.reject)
            (.step (.primeLo 2 19) <|
            .splitExp 0 4
              (.step (.grow 0 11) <|
              .step (.dropHi 3 55) <|
              .step (.dropHi 4 891) <|
              .step (.primeHi 3 53) <|
              .step (.xLo 341) <|
              .step (.xHi 341) <|
              .step (.dropLo 3 50) <|
              .step (.dropHi 3 51) <|
              .step (.primeLo 3 53) <|
              .reject)
              (.step (.dropLo 3 52) <|
              .step (.dropLo 4 387) <|
              .step (.primeLo 3 53) <|
              .step (.xLo 465) <|
              .splitBase 3 55
                (.step (.primeHi 3 53) <|
                .step (.dropLo 4 15349) <|
                .step (.xLo 15469) <|
                .splitExp 0 6
                  (.step (.grow 0 1093) <|
                  .step (.xLo 101649) <|
                  .splitExp 2 2
                    (.step (.grow 2 127) <|
                    .reject)
                    (.reject))
                  (.reject))
                (.step (.primeLo 3 59) <|
                .step (.dropHi 4 709) <|
                .step (.xHi 589) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.splitBase 3 59
                    (.reject)
                    (.step (.primeLo 3 61) <|
                    .step (.dropHi 4 506) <|
                    .step (.xHi 465) <|
                    .missing 4 233))))))
          (.step (.primeLo 3 67) <|
          .splitBase 2 17
            (.step (.dropLo 4 201) <|
            .step (.xLo 217) <|
            .splitExp 0 4
              (.step (.grow 0 11) <|
              .step (.dropHi 3 87) <|
              .step (.dropHi 4 968) <|
              .step (.primeHi 3 83) <|
              .step (.xLo 341) <|
              .step (.xHi 341) <|
              .missing 4 19)
              (.step (.dropLo 3 79) <|
              .step (.dropLo 4 764) <|
              .step (.xLo 837) <|
              .splitBase 3 83
                (.step (.dropLo 4 2052) <|
                .step (.xLo 2077) <|
                .splitBase 3 79
                  (.reject)
                  (.step (.primeLo 3 83) <|
                  .splitExp 0 6
                    (.step (.grow 0 1093) <|
                    .step (.dropHi 4 3544) <|
                    .step (.xLo 101649) <|
                    .reject)
                    (.step (.dropLo 4 12372) <|
                    .step (.xLo 12493) <|
                    .splitExp 2 2
                      (.step (.grow 2 307) <|
                      .step (.dropHi 4 35369) <|
                      .step (.xLo 47585) <|
                      .reject)
                      (.reject))))
                (.step (.primeLo 3 89) <|
                .step (.dropHi 4 1546) <|
                .step (.xHi 1457) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.step (.dropLo 4 1108) <|
                  .step (.xLo 1209) <|
                  .splitExp 2 2
                    (.missing 2 307)
                    (.step (.dropLo 4 1430) <|
                    .step (.xLo 1457) <|
                    .splitExp 0 8
                      (.missing 0 13)
                      (.reject))))))
            (.step (.primeLo 2 19) <|
            .step (.dropHi 4 288) <|
            .step (.xHi 217) <|
            .splitExp 0 4
              (.missing 0 11)
              (.step (.dropLo 3 69) <|
              .step (.dropLo 4 128) <|
              .step (.primeLo 3 71) <|
              .step (.xLo 217) <|
              .missing 4 109))))
        (.use 0))
      (.use 1))

private def deficientFour5Part043Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,47,89,2,0⟩, ⟨true,89,0,1,1⟩], 1, deficientFour5Part005⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,19,2,0⟩, ⟨false,94,0,2,0⟩, ⟨true,45,0,1,1⟩], 1, deficientFour5Part042⟩]

theorem deficientFour5Part043 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,11,19,2,0⟩, ⟨false,41,0,2,0⟩, ⟨true,21,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part043Tree deficientFour5Part043Refs _ _ (by decide +kernel)

private def deficientFour5Part044Tree : Tree :=
  .step (.primeLo 3 41) <|
  .splitExp 0 2
    (.splitBase 2 13
      (.step (.dropLo 4 33) <|
      .splitBase 3 81
        (.step (.primeHi 3 79) <|
        .step (.dropLo 4 56) <|
        .step (.xLo 57) <|
        .splitBase 2 11
          (.step (.grow 0 13) <|
          .step (.dropLo 3 63) <|
          .step (.dropLo 4 332) <|
          .step (.primeLo 3 67) <|
          .step (.xLo 377) <|
          .splitExp 1 2
            (.step (.grow 1 31) <|
            .step (.xLo 1209) <|
            .step (.dropHi 3 71) <|
            .splitExp 2 2
              (.step (.grow 2 7) <|
              .step (.grow 2 19) <|
              .step (.dropHi 3 67) <|
              .step (.dropHi 4 1398) <|
              .step (.xLo 160797) <|
              .reject)
              (.step (.dropLo 4 1212) <|
              .step (.xLo 2821) <|
              .step (.dropHi 3 68) <|
              .step (.primeHi 3 67) <|
              .reject))
            (.reject))
          (.step (.primeLo 2 13) <|
          .splitBase 3 53
            (.step (.dropLo 4 86) <|
            .step (.xLo 89) <|
            .splitExp 1 2
              (.step (.grow 1 31) <|
              .step (.dropHi 3 52) <|
              .step (.dropHi 4 178) <|
              .step (.primeHi 3 47) <|
              .step (.xLo 93) <|
              .step (.xHi 93) <|
              .step (.fix 4 47 3) <|
              .reject)
              (.step (.dropLo 3 43) <|
              .step (.dropLo 4 252) <|
              .step (.xLo 253) <|
              .splitBase 3 47
                (.step (.dropLo 4 660) <|
                .step (.xLo 661) <|
                .splitBase 3 43
                  (.reject)
                  (.step (.primeLo 3 47) <|
                  .step (.dropHi 4 1369) <|
                  .splitExp 2 2
                    (.step (.grow 2 61) <|
                    .step (.dropHi 4 843) <|
                    .step (.xLo 793) <|
                    .step (.xHi 793) <|
                    .missing 4 397)
                    (.step (.dropLo 4 941) <|
                    .splitExp 1 4
                      (.step (.grow 1 11) <|
                      .missing 1 71)
                      (.step (.dropLo 4 1324) <|
                      .step (.xLo 1325) <|
                      .splitExp 1 6
                        (.step (.dropHi 4 1345) <|
                        .splitExp 3 2
                          (.missing 3 37)
                          (.step (.dropLo 4 1342) <|
                          .step (.xLo 1345) <|
                          .missing 4 673))
                        (.step (.dropLo 4 1346) <|
                        .step (.xLo 1349) <|
                        .splitExp 3 2
                          (.step (.grow 3 37) <|
                          .missing 3 61)
                          (.step (.dropLo 4 1364) <|
                          .step (.xLo 1365) <|
                          .splitExp 2 4
                            (.reject)
                            (.step (.dropLo 4 1369) <|
                            .missing 4 137)))))))
                (.step (.primeLo 3 53) <|
                .step (.dropHi 4 313) <|
                .splitExp 2 2
                  (.step (.grow 2 61) <|
                  .step (.dropHi 4 273) <|
                  .step (.xLo 305) <|
                  .reject)
                  (.step (.dropLo 4 284) <|
                  .step (.xLo 285) <|
                  .splitExp 1 4
                    (.step (.grow 1 11) <|
                    .missing 1 71)
                    (.step (.dropLo 4 312) <|
                    .step (.xLo 313) <|
                    .missing 4 157)))))
            (.use 0)))
        (.use 1))
      (.step (.primeLo 2 17) <|
      .step (.grow 0 13) <|
      .step (.dropHi 4 58) <|
      .step (.xLo 65) <|
      .reject))
    (.use 2)

private def deficientFour5Part044Refs : List Known := [
  ⟨#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,54,79,2,0⟩, ⟨true,57,0,1,1⟩], 1, deficientFour5Part000⟩,
  ⟨#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,82,0,2,0⟩, ⟨true,33,0,1,1⟩], 1, deficientFour5Part004⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,11,19,2,0⟩, ⟨false,41,0,2,0⟩, ⟨true,21,0,1,1⟩], 1, deficientFour5Part043⟩]

theorem deficientFour5Part044 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,11,19,2,0⟩, ⟨false,38,0,2,0⟩, ⟨true,21,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part044Tree deficientFour5Part044Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
