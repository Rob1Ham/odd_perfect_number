module

public import OddPerfect.DeficientPowerReplayGeneral.Part019

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart095Tree : Tree :=
  .step (.dropLo 2 57) <|
  .step (.primeLo 2 59) <|
  .splitBase 3 133
    (.step (.primeHi 3 131) <|
    .step (.dropLo 2 66) <|
    .step (.primeLo 2 67) <|
    .splitBase 2 71
      (.step (.dropLo 3 117) <|
      .step (.primeLo 3 127) <|
      .step (.dropHi 2 70) <|
      .step (.primeHi 2 67) <|
      .step (.dropLo 3 130) <|
      .step (.primeLo 3 131) <|
      .splitExp 1 2
        (.missing 1 61)
        (.reject))
      (.step (.primeLo 2 73) <|
      .step (.dropHi 3 118) <|
      .step (.primeHi 3 113) <|
      .splitBase 2 75
        (.step (.primeHi 2 73) <|
        .step (.dropLo 3 112) <|
        .step (.primeLo 3 113) <|
        .splitExp 1 2
          (.missing 1 61)
          (.reject))
        (.step (.primeLo 2 79) <|
        .step (.dropHi 3 105) <|
        .step (.primeHi 3 103) <|
        .splitExp 1 2
          (.missing 1 61)
          (.reject))))
    (.step (.primeLo 3 137) <|
    .step (.dropHi 2 67) <|
    .splitBase 3 159
      (.step (.primeHi 3 157) <|
      .step (.dropLo 2 61) <|
      .splitBase 2 63
        (.step (.primeHi 2 61) <|
        .reject)
        (.step (.primeLo 2 67) <|
        .step (.dropHi 3 139) <|
        .splitExp 1 2
          (.missing 1 61)
          (.step (.dropLo 3 138) <|
          .step (.primeLo 3 139) <|
          .splitSpecial 5
            (.missing 4 7)
            (.reject))))
      (.step (.primeLo 3 163) <|
      .step (.dropHi 2 62) <|
      .step (.primeHi 2 61) <|
      .splitBase 3 175
        (.step (.primeHi 3 173) <|
        .splitExp 1 2
          (.step (.fix 1 61 2) <|
          .reject)
          (.reject))
        (.step (.primeLo 3 179) <|
        .step (.dropHi 2 60) <|
        .step (.primeHi 2 59) <|
        .splitExp 1 2
          (.missing 1 61)
          (.reject))))

theorem deficientFourPowerGeneralPart095 : Closed (#v[⟨false,3,3,2,2⟩, ⟨false,13,13,2,0⟩, ⟨false,47,79,2,0⟩, ⟨false,103,191,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart095Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart096Tree : Tree :=
  .step (.primeLo 3 331) <|
  .step (.dropHi 2 134) <|
  .step (.primeHi 2 131) <|
  .splitExp 0 6
    (.missing 0 1093)
    (.splitBase 3 357
      (.step (.primeHi 3 353) <|
      .splitBase 2 127
        (.reject)
        (.step (.primeLo 2 131) <|
        .splitExp 1 2
          (.missing 1 127)
          (.step (.dropLo 3 342) <|
          .step (.primeLo 3 347) <|
          .splitSpecial 5
            (.missing 4 7)
            (.step (.dropLo 3 350) <|
            .step (.primeLo 3 353) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject)))))
      (.step (.primeLo 3 359) <|
      .step (.dropHi 2 130) <|
      .step (.primeHi 2 127) <|
      .splitBase 3 373
        (.splitExp 1 2
          (.step (.dropHi 3 369) <|
          .step (.primeHi 3 367) <|
          .splitSpecial 5
            (.missing 4 7)
            (.step (.dropLo 3 362) <|
            .step (.primeLo 3 367) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject)))
          (.reject))
        (.step (.primeLo 3 379) <|
        .splitExp 1 2
          (.reject)
          (.splitSpecial 5
            (.missing 4 7)
            (.step (.dropLo 3 382) <|
            .step (.primeLo 3 383) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject))))))

theorem deficientFourPowerGeneralPart096 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,127,139,2,0⟩, ⟨false,324,389,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart096Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart097Tree : Tree :=
  .step (.primeHi 3 523) <|
  .step (.dropLo 2 108) <|
  .step (.primeLo 2 109) <|
  .splitBase 2 121
    (.step (.primeHi 2 113) <|
    .step (.dropLo 3 444) <|
    .step (.primeLo 3 449) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.reject))
    (.step (.primeLo 2 127) <|
    .step (.dropHi 3 390) <|
    .step (.primeHi 3 389) <|
    .splitBase 3 323
      (.step (.primeHi 3 317) <|
      .splitBase 2 131
        (.step (.dropLo 3 288) <|
        .step (.primeLo 3 293) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.reject))
        (.step (.primeLo 2 137) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 3 285) <|
          .step (.primeLo 3 293) <|
          .splitBase 3 303
            (.step (.primeHi 3 293) <|
            .splitExp 1 2
              (.missing 1 127)
              (.reject))
            (.step (.primeLo 3 307) <|
            .splitExp 1 2
              (.missing 1 127)
              (.splitBase 2 137
                (.splitBase 3 311
                  (.splitSpecial 5
                    (.missing 4 7)
                    (.reject))
                  (.step (.primeLo 3 313) <|
                  .splitSpecial 5
                    (.missing 4 7)
                    (.splitExp 0 8
                      (.missing 0 13)
                      (.reject))))
                (.step (.primeLo 2 139) <|
                .step (.dropHi 3 308) <|
                .step (.primeHi 3 307) <|
                .splitSpecial 5
                  (.missing 4 7)
                  (.splitExp 0 8
                    (.missing 0 13)
                    (.reject))))))))
      (.use 0))

private def deficientFourPowerGeneralPart097Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,127,139,2,0⟩, ⟨false,324,389,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart096⟩]

theorem deficientFourPowerGeneralPart097 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,139,2,0⟩, ⟨false,277,537,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart097Tree deficientFourPowerGeneralPart097Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart098Tree : Tree :=
  .step (.primeLo 3 683) <|
  .step (.dropHi 2 111) <|
  .step (.primeHi 2 109) <|
  .splitExp 0 6
    (.missing 0 1093)
    (.splitBase 3 783
      (.step (.primeHi 3 773) <|
      .splitExp 1 2
        (.missing 1 127)
        (.step (.dropLo 2 108) <|
        .step (.dropLo 3 730) <|
        .step (.primeLo 2 109) <|
        .step (.primeLo 3 733) <|
        .splitSpecial 5
          (.missing 4 7)
          (.step (.dropLo 3 765) <|
          .step (.primeLo 3 769) <|
          .splitExp 0 8
            (.missing 0 13)
            (.reject))))
      (.step (.primeLo 3 787) <|
      .splitExp 1 2
        (.missing 1 127)
        (.splitBase 3 847
          (.step (.primeHi 3 839) <|
          .splitBase 2 107
            (.step (.dropLo 3 835) <|
            .step (.primeLo 3 839) <|
            .splitSpecial 5
              (.missing 4 7)
              (.reject))
            (.step (.primeLo 2 109) <|
            .step (.dropHi 3 797) <|
            .splitSpecial 5
              (.missing 4 7)
              (.splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 3 793) <|
                .step (.primeLo 3 797) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.splitExp 2 2
                    (.missing 2 7)
                    (.splitExp 0 12
                      (.splitExp 1 4
                        (.missing 1 151)
                        (.reject))
                      (.reject)))))))
          (.step (.primeLo 3 853) <|
          .step (.dropHi 2 108) <|
          .step (.primeHi 2 107) <|
          .splitSpecial 5
            (.missing 4 7)
            (.step (.dropLo 3 882) <|
            .step (.primeLo 3 883) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject))))))

theorem deficientFourPowerGeneralPart098 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,107,113,2,0⟩, ⟨false,682,919,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart098Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart099Tree : Tree :=
  .step (.primeHi 3 1847) <|
  .splitExp 0 6
    (.step (.fix 0 1093 3) <|
    .step (.dropLo 2 98) <|
    .step (.dropHi 2 100) <|
    .step (.primeLo 2 101) <|
    .reject)
    (.step (.dropLo 2 98) <|
    .step (.primeLo 2 101) <|
    .splitBase 3 1323
      (.step (.primeHi 3 1321) <|
      .splitBase 3 1157
        (.step (.primeHi 3 1153) <|
        .splitExp 1 2
          (.missing 1 127)
          (.reject))
        (.step (.primeLo 3 1163) <|
        .splitExp 1 2
          (.missing 1 127)
          (.step (.dropLo 2 102) <|
          .step (.dropLo 3 1203) <|
          .step (.primeLo 2 103) <|
          .step (.primeLo 3 1213) <|
          .splitSpecial 5
            (.missing 4 7)
            (.step (.dropLo 3 1303) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject)))))
      (.step (.primeLo 3 1327) <|
      .splitBase 3 1543
        (.splitExp 1 2
          (.missing 1 127)
          (.splitBase 2 101
            (.reject)
            (.step (.primeLo 2 103) <|
            .step (.dropHi 3 1398) <|
            .step (.primeHi 3 1381) <|
            .splitSpecial 5
              (.missing 4 7)
              (.splitExp 0 8
                (.missing 0 13)
                (.reject)))))
        (.step (.primeLo 3 1549) <|
        .step (.dropHi 2 102) <|
        .step (.primeHi 2 101) <|
        .splitExp 1 2
          (.missing 1 127)
          (.step (.dropLo 3 1569) <|
          .step (.primeLo 3 1571) <|
          .splitBase 3 1697
            (.splitSpecial 5
              (.missing 4 7)
              (.reject))
            (.step (.primeLo 3 1699) <|
            .splitSpecial 5
              (.missing 4 7)
              (.step (.dropLo 3 1744) <|
              .step (.primeLo 3 1747) <|
              .splitExp 0 8
                (.missing 0 13)
                (.reject)))))))

theorem deficientFourPowerGeneralPart099 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,103,2,0⟩, ⟨false,1031,1853,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart099Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
