module

public import OddPerfect.DeficientPowerReplayGeneral.Part003

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart015Tree : Tree :=
  .step (.dropLo 3 66) <|
  .step (.dropLo 4 266) <|
  .step (.primeLo 3 67) <|
  .step (.xLo 269) <|
  .splitBase 2 17
    (.reject)
    (.step (.primeLo 2 19) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.xLo 297) <|
      .splitBase 3 75
        (.step (.primeHi 3 73) <|
        .step (.dropLo 4 787) <|
        .step (.xLo 825) <|
        .splitBase 3 69
          (.step (.primeHi 3 67) <|
          .step (.dropLo 4 37994) <|
          .step (.xLo 38005) <|
          .splitExp 1 4
            (.step (.grow 1 71) <|
            .step (.xLo 38269) <|
            .splitExp 2 2
              (.step (.grow 2 127) <|
              .step (.dropHi 4 43487) <|
              .step (.xLo 297561) <|
              .reject)
              (.reject))
            (.reject))
          (.step (.primeLo 3 71) <|
          .step (.dropHi 4 2437) <|
          .step (.xHi 2409) <|
          .splitExp 1 4
            (.step (.fix 1 71 3) <|
            .step (.dropLo 4 1138) <|
            .step (.dropHi 4 1369) <|
            .step (.xLo 1177) <|
            .step (.xHi 1353) <|
            .splitExp 2 2
              (.missing 2 127)
              (.reject))
            (.step (.dropLo 4 1039) <|
            .step (.xLo 1045) <|
            .splitBase 3 71
              (.step (.dropLo 4 1749) <|
              .splitExp 2 2
                (.missing 2 127)
                (.step (.dropLo 4 2345) <|
                .step (.xLo 2365) <|
                .splitExp 1 6
                  (.reject)
                  (.reject)))
              (.step (.primeLo 3 73) <|
              .step (.dropHi 4 1247) <|
              .step (.xHi 1221) <|
              .splitExp 2 2
                (.missing 2 127)
                (.reject)))))
        (.step (.primeLo 3 79) <|
        .step (.dropHi 4 539) <|
        .step (.xHi 517) <|
        .splitBase 3 83
          (.step (.dropLo 4 340) <|
          .step (.xLo 341) <|
          .splitBase 3 79
            (.step (.dropLo 4 430) <|
            .step (.xLo 473) <|
            .splitExp 1 4
              (.missing 1 71)
              (.step (.dropLo 4 496) <|
              .step (.xLo 517) <|
              .missing 4 7))
            (.step (.primeLo 3 83) <|
            .step (.dropHi 4 404) <|
            .step (.xHi 385) <|
            .splitExp 1 4
              (.missing 1 71)
              (.step (.dropLo 4 380) <|
              .step (.xLo 385) <|
              .missing 4 193)))
          (.step (.primeLo 3 89) <|
          .step (.dropHi 4 303) <|
          .step (.xHi 297) <|
          .missing 4 149)))
      (.step (.dropLo 3 88) <|
      .step (.dropLo 4 10377) <|
      .step (.primeLo 3 89) <|
      .splitExp 0 6
        (.step (.grow 0 1093) <|
        .step (.xLo 14209) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .step (.grow 1 71) <|
          .step (.xLo 853633) <|
          .splitExp 2 2
            (.step (.grow 2 127) <|
            .reject)
            (.reject))
          (.reject))
        (.reject)))

theorem deficientFourPowerGeneralPart015 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,47,89,2,0⟩, ⟨true,89,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart015Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart016Tree : Tree :=
  .step (.primeHi 3 151) <|
  .step (.dropLo 4 522) <|
  .step (.xLo 561) <|
  .splitBase 3 137
    (.step (.dropLo 4 809) <|
    .step (.xLo 825) <|
    .splitBase 3 131
      (.step (.dropLo 4 1113) <|
      .step (.xLo 1133) <|
      .splitExp 1 4
        (.step (.grow 1 71) <|
        .step (.dropHi 4 2210) <|
        .step (.xLo 3905) <|
        .reject)
        (.step (.dropLo 4 1690) <|
        .step (.xLo 1705) <|
        .splitExp 2 2
          (.step (.grow 2 307) <|
          .step (.dropHi 4 2976) <|
          .step (.xLo 3377) <|
          .reject)
          (.step (.dropLo 4 2573) <|
          .step (.xLo 2585) <|
          .splitBase 3 127
            (.step (.dropLo 4 6829) <|
            .step (.xLo 6853) <|
            .splitExp 1 6
              (.step (.dropHi 4 6885) <|
              .step (.xHi 6853) <|
              .missing 4 23)
              (.step (.dropLo 4 7455) <|
              .step (.xLo 7469) <|
              .splitExp 2 4
                (.step (.dropHi 4 7511) <|
                .step (.xHi 7469) <|
                .missing 4 83)
                (.step (.dropLo 4 7494) <|
                .step (.xLo 7513) <|
                .missing 4 13)))
            (.step (.primeLo 3 131) <|
            .step (.dropHi 4 2668) <|
            .step (.xHi 2629) <|
            .splitExp 1 6
              (.reject)
              (.reject)))))
      (.step (.primeLo 3 137) <|
      .step (.dropHi 4 1405) <|
      .step (.xHi 1397) <|
      .splitExp 1 4
        (.missing 1 71)
        (.step (.dropLo 4 1077) <|
        .step (.xLo 1089) <|
        .splitExp 2 2
          (.missing 2 307)
          (.step (.dropLo 4 1378) <|
          .step (.xLo 1397) <|
          .missing 4 233))))
    (.step (.primeLo 3 139) <|
    .step (.dropHi 4 1223) <|
    .step (.xHi 1221) <|
    .splitBase 3 143
      (.step (.primeHi 3 139) <|
      .step (.dropLo 4 746) <|
      .step (.xLo 781) <|
      .splitExp 1 4
        (.step (.grow 1 71) <|
        .step (.dropHi 4 879) <|
        .step (.xHi 781) <|
        .missing 4 23)
        (.step (.dropLo 4 967) <|
        .step (.xLo 1001) <|
        .splitExp 2 2
          (.missing 2 307)
          (.step (.dropLo 4 1203) <|
          .step (.xLo 1221) <|
          .missing 4 13)))
      (.step (.primeLo 3 149) <|
      .step (.dropHi 4 767) <|
      .step (.xHi 737) <|
      .splitExp 1 4
        (.missing 1 71)
        (.step (.dropLo 4 621) <|
        .step (.xLo 649) <|
        .splitExp 2 2
          (.missing 2 307)
          (.step (.dropLo 4 711) <|
          .step (.xLo 737) <|
          .missing 4 41))))

theorem deficientFourPowerGeneralPart016 : Closed (#v[⟨false,3,3,4,4⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,127,153,2,0⟩, ⟨true,297,7513,5,0⟩] : Vector Slot 5) 11 :=
  Tree.sound deficientFourPowerGeneralPart016Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart017Tree : Tree :=
  .step (.dropLo 4 8608) <|
  .step (.xLo 8609) <|
  .splitExp 0 10
    (.step (.grow 0 23) <|
    .step (.dropHi 4 8760) <|
    .step (.xLo 8625) <|
    .step (.xHi 8717) <|
    .splitExp 3 2
      (.step (.dropHi 4 8677) <|
      .step (.xHi 8625) <|
      .missing 4 227)
      (.step (.dropLo 4 8690) <|
      .step (.xLo 8717) <|
      .missing 4 1453))
    (.step (.dropLo 4 8997) <|
    .splitExp 3 2
      (.step (.dropHi 4 9123) <|
      .step (.xHi 9121) <|
      .splitExp 0 12
        (.step (.dropHi 4 9071) <|
        .step (.xHi 9069) <|
        .splitExp 1 8
          (.step (.grow 1 31) <|
          .missing 1 829)
          (.step (.dropLo 4 9037) <|
          .splitExp 2 4
            (.missing 2 151)
            (.reject)))
        (.step (.dropLo 4 9042) <|
        .step (.xLo 9045) <|
        .splitExp 1 8
          (.missing 1 31)
          (.step (.dropLo 4 9082) <|
          .step (.xLo 9085) <|
          .splitExp 2 4
            (.missing 2 151)
            (.step (.dropLo 4 9116) <|
            .step (.xLo 9117) <|
            .splitExp 0 14
              (.missing 0 11)
              (.reject)))))
      (.step (.dropLo 4 9086) <|
      .step (.xLo 9089) <|
      .splitExp 0 12
        (.step (.dropHi 4 9163) <|
        .step (.xHi 9161) <|
        .splitExp 1 8
          (.step (.grow 1 31) <|
          .missing 1 829)
          (.step (.dropLo 4 9127) <|
          .step (.xLo 9129) <|
          .splitExp 2 4
            (.missing 2 151)
            (.reject)))
        (.step (.dropLo 4 9133) <|
        .splitExp 1 8
          (.step (.grow 1 31) <|
          .missing 1 829)
          (.step (.dropLo 4 9174) <|
          .step (.xLo 9177) <|
          .splitExp 2 4
            (.missing 2 151)
            (.step (.dropLo 4 9208) <|
            .step (.xLo 9209) <|
            .splitExp 0 14
              (.missing 0 11)
              (.reject))))))

theorem deficientFourPowerGeneralPart017 : Closed (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,7785,9213,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart017Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart018Tree : Tree :=
  .step (.dropLo 4 692) <|
  .step (.xLo 693) <|
  .splitExp 0 6
    (.step (.grow 0 1093) <|
    .step (.dropHi 4 1767) <|
    .step (.xLo 1093) <|
    .step (.xHi 1093) <|
    .missing 4 547)
    (.step (.dropLo 4 963) <|
    .step (.xLo 965) <|
    .splitExp 1 4
      (.step (.grow 1 11) <|
      .step (.grow 1 71) <|
      .step (.dropHi 4 2333) <|
      .step (.xLo 3905) <|
      .reject)
      (.step (.dropLo 4 1367) <|
      .step (.xLo 1369) <|
      .splitBase 3 97
        (.step (.dropLo 4 3135) <|
        .step (.xLo 3137) <|
        .splitExp 2 2
          (.step (.grow 2 127) <|
          .step (.dropHi 4 3932) <|
          .step (.xLo 3429) <|
          .step (.xHi 3429) <|
          .missing 4 7)
          (.step (.dropLo 4 5760) <|
          .step (.xLo 5761) <|
          .splitExp 0 8
            (.step (.grow 0 13) <|
            .missing 0 757)
            (.step (.dropLo 4 7785) <|
            .splitExp 1 6
              (.step (.dropHi 4 8243) <|
              .step (.xHi 8241) <|
              .splitExp 0 10
                (.step (.grow 0 23) <|
                .step (.dropHi 4 7877) <|
                .step (.xLo 7797) <|
                .step (.xHi 7797) <|
                .missing 4 7)
                (.step (.dropLo 4 8101) <|
                .splitExp 3 2
                  (.step (.dropHi 4 8169) <|
                  .splitExp 0 12
                    (.step (.dropHi 4 8128) <|
                    .step (.xHi 8125) <|
                    .splitExp 2 4
                      (.missing 2 151)
                      (.reject))
                    (.step (.dropLo 4 8138) <|
                    .step (.xLo 8141) <|
                    .splitExp 2 4
                      (.missing 2 151)
                      (.step (.dropLo 4 8165) <|
                      .splitExp 0 14
                        (.missing 0 11)
                        (.reject))))
                  (.step (.dropLo 4 8174) <|
                  .step (.xLo 8177) <|
                  .splitExp 0 12
                    (.step (.dropHi 4 8201) <|
                    .splitExp 2 4
                      (.missing 2 151)
                      (.reject))
                    (.step (.dropLo 4 8211) <|
                    .step (.xLo 8213) <|
                    .splitExp 2 4
                      (.missing 2 151)
                      (.step (.dropLo 4 8238) <|
                      .step (.xLo 8241) <|
                      .missing 4 13)))))
              (.use 0))))
        (.step (.primeLo 3 101) <|
        .step (.dropHi 4 1920) <|
        .step (.xHi 1917) <|
        .splitExp 2 2
          (.step (.grow 2 127) <|
          .step (.dropHi 4 1500) <|
          .step (.xLo 1397) <|
          .step (.xHi 1397) <|
          .missing 4 233)
          (.step (.dropLo 4 1707) <|
          .step (.xLo 1709) <|
          .splitExp 0 8
            (.step (.grow 0 13) <|
            .missing 0 757)
            (.step (.dropLo 4 1849) <|
            .splitExp 1 6
              (.step (.dropHi 4 1873) <|
              .splitExp 0 10
                (.missing 0 23)
                (.step (.dropLo 4 1866) <|
                .step (.xLo 1869) <|
                .splitExp 3 2
                  (.step (.dropHi 4 1870) <|
                  .step (.xHi 1869) <|
                  .missing 4 11)
                  (.step (.dropLo 4 1870) <|
                  .step (.xLo 1873) <|
                  .missing 4 937)))
              (.step (.dropLo 4 1892) <|
              .step (.xLo 1893) <|
              .splitExp 0 10
                (.step (.grow 0 23) <|
                .step (.dropHi 4 1899) <|
                .step (.xLo 1909) <|
                .reject)
                (.step (.dropLo 4 1910) <|
                .step (.xLo 1913) <|
                .splitExp 3 2
                  (.step (.dropHi 4 1916) <|
                  .step (.xHi 1913) <|
                  .missing 4 11)
                  (.step (.dropLo 4 1914) <|
                  .step (.xLo 1917) <|
                  .missing 4 7))))))))

private def deficientFourPowerGeneralPart018Refs : List Known := [
  ⟨#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨true,7785,9213,5,0⟩], 1, deficientFourPowerGeneralPart017⟩]

theorem deficientFourPowerGeneralPart018 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,101,2,0⟩, ⟨true,461,9213,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart018Tree deficientFourPowerGeneralPart018Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart019Tree : Tree :=
  .step (.dropLo 4 459) <|
  .step (.xLo 461) <|
  .splitBase 3 101
    (.use 0)
    (.step (.primeLo 3 103) <|
    .step (.dropHi 4 1398) <|
    .step (.xHi 1397) <|
    .splitExp 0 6
      (.step (.grow 0 1093) <|
      .step (.dropHi 4 853) <|
      .step (.xLo 1093) <|
      .reject)
      (.step (.dropLo 4 564) <|
      .step (.xLo 565) <|
      .splitBase 3 105
        (.step (.primeHi 3 103) <|
        .step (.dropLo 4 811) <|
        .step (.xLo 813) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .missing 1 71)
          (.step (.dropLo 4 1081) <|
          .splitExp 2 2
            (.step (.grow 2 127) <|
            .step (.dropHi 4 1162) <|
            .step (.xLo 1397) <|
            .reject)
            (.step (.dropLo 4 1282) <|
            .step (.xLo 1285) <|
            .splitExp 0 8
              (.step (.grow 0 13) <|
              .missing 0 757)
              (.step (.dropLo 4 1361) <|
              .splitExp 1 6
                (.step (.dropHi 4 1374) <|
                .step (.xHi 1373) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 4 1370) <|
                  .step (.xLo 1373) <|
                  .missing 4 229))
                (.step (.dropLo 4 1384) <|
                .step (.xLo 1385) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 4 1394) <|
                  .step (.xLo 1397) <|
                  .missing 4 233))))))
        (.step (.primeLo 3 107) <|
        .step (.dropHi 4 925) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .step (.grow 1 71) <|
          .step (.dropHi 4 713) <|
          .step (.xLo 781) <|
          .reject)
          (.step (.dropLo 4 683) <|
          .step (.xLo 685) <|
          .splitExp 2 2
            (.step (.grow 2 127) <|
            .step (.dropHi 4 815) <|
            .step (.xLo 889) <|
            .reject)
            (.step (.dropLo 4 758) <|
            .step (.xLo 761) <|
            .splitBase 3 107
              (.step (.dropLo 4 872) <|
              .step (.xLo 873) <|
              .splitExp 0 8
                (.step (.grow 0 13) <|
                .missing 0 757)
                (.step (.dropLo 4 908) <|
                .step (.xLo 909) <|
                .splitExp 1 6
                  (.step (.dropHi 4 914) <|
                  .step (.xHi 913) <|
                  .splitExp 0 10
                    (.missing 0 23)
                    (.step (.dropLo 4 912) <|
                    .step (.xLo 913) <|
                    .missing 4 457))
                  (.step (.dropLo 4 918) <|
                  .step (.xLo 921) <|
                  .splitExp 0 10
                    (.missing 0 23)
                    (.step (.dropLo 4 923) <|
                    .step (.xLo 925) <|
                    .missing 4 463))))
              (.step (.primeLo 3 109) <|
              .step (.dropHi 4 797) <|
              .splitExp 0 8
                (.step (.grow 0 13) <|
                .missing 0 757)
                (.step (.dropLo 4 785) <|
                .splitExp 1 6
                  (.step (.dropHi 4 789) <|
                  .splitExp 0 10
                    (.missing 0 23)
                    (.step (.dropLo 4 788) <|
                    .step (.xLo 789) <|
                    .missing 4 79))
                  (.step (.dropLo 4 792) <|
                  .step (.xLo 793) <|
                  .splitExp 0 10
                    (.missing 0 23)
                    (.step (.dropLo 4 796) <|
                    .step (.xLo 797) <|
                    .missing 4 7)))))))))

private def deficientFourPowerGeneralPart019Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,101,2,0⟩, ⟨true,461,9213,5,0⟩], 1, deficientFourPowerGeneralPart018⟩]

theorem deficientFourPowerGeneralPart019 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,109,2,0⟩, ⟨true,289,9213,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart019Tree deficientFourPowerGeneralPart019Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
