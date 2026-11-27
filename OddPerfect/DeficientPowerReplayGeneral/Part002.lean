module

public import OddPerfect.DeficientPowerReplayGeneral.Part001

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart005Tree : Tree :=
  .step (.primeLo 3 79) <|
  .splitBase 2 11
    (.step (.grow 0 13) <|
    .step (.dropLo 4 63) <|
    .step (.xLo 65) <|
    .splitBase 3 157
      (.step (.dropLo 4 107) <|
      .step (.xLo 117) <|
      .splitExp 1 2
        (.step (.grow 1 31) <|
        .step (.dropHi 3 156) <|
        .step (.dropHi 4 442) <|
        .step (.primeHi 3 151) <|
        .step (.xLo 1209) <|
        .reject)
        (.step (.dropLo 3 124) <|
        .step (.dropLo 4 606) <|
        .step (.primeLo 3 127) <|
        .step (.xLo 637) <|
        .splitBase 3 139
          (.step (.dropLo 4 1219) <|
          .step (.xLo 1261) <|
          .splitExp 2 2
            (.step (.grow 2 7) <|
            .step (.grow 2 19) <|
            .step (.xLo 1729) <|
            .splitBase 3 131
              (.step (.dropLo 4 2646) <|
              .step (.xLo 8645) <|
              .splitExp 1 4
                (.step (.grow 1 71) <|
                .reject)
                (.step (.dropLo 3 129) <|
                .step (.dropLo 4 14157) <|
                .step (.primeLo 3 131) <|
                .step (.xLo 15561) <|
                .step (.dropHi 4 17424) <|
                .step (.xHi 15561) <|
                .missing 4 31))
              (.step (.primeLo 3 137) <|
              .step (.dropHi 4 2537) <|
              .step (.xHi 1729) <|
              .missing 4 173))
            (.step (.dropLo 3 137) <|
            .step (.dropLo 4 13324) <|
            .step (.xLo 13325) <|
            .splitExp 1 4
              (.step (.grow 1 71) <|
              .step (.xLo 13845) <|
              .splitBase 3 137
                (.reject)
                (.step (.primeLo 3 139) <|
                .step (.dropHi 4 14604) <|
                .step (.xHi 13845) <|
                .missing 4 7))
              (.reject)))
          (.step (.primeLo 3 149) <|
          .step (.dropHi 4 4262) <|
          .step (.xHi 4225) <|
          .splitExp 2 2
            (.step (.grow 2 7) <|
            .step (.grow 2 19) <|
            .step (.dropHi 4 1014) <|
            .step (.xLo 1729) <|
            .reject)
            (.step (.dropLo 4 1104) <|
            .step (.xLo 1105) <|
            .splitExp 1 4
              (.step (.grow 1 71) <|
              .step (.dropHi 4 1803) <|
              .step (.xLo 2769) <|
              .reject)
              (.step (.dropLo 4 1672) <|
              .step (.xLo 1677) <|
              .splitBase 3 151
                (.step (.dropLo 4 2912) <|
                .step (.xLo 2925) <|
                .splitBase 3 149
                  (.step (.dropLo 4 3938) <|
                  .step (.xLo 3965) <|
                  .splitExp 1 6
                    (.step (.dropHi 4 4041) <|
                    .step (.xHi 4017) <|
                    .splitExp 2 4
                      (.reject)
                      (.reject))
                    (.step (.dropLo 4 4138) <|
                    .step (.xLo 4173) <|
                    .splitExp 2 4
                      (.reject)
                      (.reject)))
                  (.step (.primeLo 3 151) <|
                  .step (.dropHi 4 3085) <|
                  .step (.xHi 3081) <|
                  .splitExp 1 6
                    (.step (.dropHi 4 2968) <|
                    .step (.xHi 2925) <|
                    .missing 4 7)
                    (.step (.dropLo 4 3020) <|
                    .step (.xLo 3029) <|
                    .splitExp 2 4
                      (.reject)
                      (.step (.dropLo 4 3077) <|
                      .step (.xLo 3081) <|
                      .missing 4 23))))
                (.step (.primeLo 3 157) <|
                .step (.dropHi 4 1728) <|
                .step (.xHi 1677) <|
                .missing 4 839))))))
      (.step (.primeLo 3 163) <|
      .step (.dropHi 4 1227) <|
      .step (.xHi 1209) <|
      .splitExp 1 2
        (.step (.grow 1 31) <|
        .step (.dropHi 4 113) <|
        .step (.xLo 1209) <|
        .reject)
        (.use 0)))
    (.use 1)

private def deficientFourPowerGeneralPart005Refs : List Known := [
  ⟨#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,163,0,2,0⟩, ⟨true,65,1209,5,0⟩], 13, deficientFourPowerGeneralPart002⟩,
  ⟨#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,12,13,2,0⟩, ⟨false,79,0,2,0⟩, ⟨true,33,0,5,0⟩], 1, deficientFourPowerGeneralPart004⟩]

theorem deficientFourPowerGeneralPart005 : Closed (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,74,0,2,0⟩, ⟨true,33,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart005Tree deficientFourPowerGeneralPart005Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart006Tree : Tree :=
  .step (.dropLo 4 91) <|
  .step (.xLo 93) <|
  .splitBase 3 25
    (.step (.primeHi 3 23) <|
    .step (.dropLo 4 607) <|
    .step (.xLo 609) <|
    .splitExp 0 4
      (.splitExp 1 2
        (.step (.grow 1 19) <|
        .step (.dropHi 4 1230) <|
        .step (.xLo 665) <|
        .step (.xHi 1197) <|
        .splitExp 2 2
          (.reject)
          (.step (.dropLo 4 1110) <|
          .step (.xLo 1121) <|
          .splitExp 3 2
            (.missing 3 79)
            (.reject)))
        (.reject))
      (.reject))
    (.step (.primeLo 3 29) <|
    .step (.dropHi 4 320) <|
    .step (.xHi 317) <|
    .splitExp 0 4
      (.step (.dropHi 4 138) <|
      .step (.xHi 137) <|
      .splitExp 1 2
        (.step (.grow 1 19) <|
        .step (.dropHi 4 98) <|
        .step (.xLo 133) <|
        .reject)
        (.step (.dropLo 4 123) <|
        .step (.xLo 125) <|
        .splitExp 2 2
          (.step (.grow 2 19) <|
          .step (.dropHi 4 125) <|
          .step (.xLo 133) <|
          .reject)
          (.step (.dropLo 4 136) <|
          .step (.xLo 137) <|
          .missing 4 23)))
      (.step (.dropLo 4 137) <|
      .splitExp 1 2
        (.step (.grow 1 19) <|
        .step (.dropHi 4 165) <|
        .step (.xLo 209) <|
        .reject)
        (.step (.dropLo 4 225) <|
        .splitExp 2 2
          (.step (.grow 2 19) <|
          .step (.dropHi 4 258) <|
          .step (.xLo 285) <|
          .reject)
          (.step (.dropLo 4 271) <|
          .step (.xLo 273) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 304) <|
            .step (.xLo 305) <|
            .splitExp 1 4
              (.step (.dropHi 4 314) <|
              .step (.xHi 313) <|
              .splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 4 308) <|
                .step (.xLo 309) <|
                .splitExp 3 2
                  (.missing 3 13)
                  (.step (.dropLo 4 312) <|
                  .step (.xLo 313) <|
                  .missing 4 157)))
              (.step (.dropLo 4 310) <|
              .step (.xLo 313) <|
              .splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 4 314) <|
                .step (.xLo 317) <|
                .missing 4 53)))))))

theorem deficientFourPowerGeneralPart006 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,23,29,2,0⟩, ⟨true,41,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart006Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart007Tree : Tree :=
  .step (.dropLo 4 44) <|
  .step (.xLo 45) <|
  .splitBase 3 35
    (.step (.primeHi 3 31) <|
    .step (.dropLo 4 75) <|
    .step (.xLo 77) <|
    .splitExp 0 4
      (.step (.dropHi 4 105) <|
      .splitExp 1 2
        (.missing 1 19)
        (.step (.dropLo 4 96) <|
        .step (.xLo 97) <|
        .splitExp 2 2
          (.missing 2 19)
          (.step (.dropLo 4 104) <|
          .step (.xLo 105) <|
          .missing 4 53)))
      (.step (.dropLo 4 104) <|
      .step (.xLo 105) <|
      .splitExp 1 2
        (.step (.grow 1 19) <|
        .step (.dropHi 4 120) <|
        .step (.xLo 133) <|
        .reject)
        (.step (.dropLo 4 149) <|
        .splitExp 2 2
          (.missing 2 19)
          (.step (.dropLo 4 167) <|
          .step (.xLo 169) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 179) <|
            .step (.xLo 181) <|
            .missing 4 13)))))
    (.step (.primeLo 3 37) <|
    .step (.dropHi 4 92) <|
    .step (.xHi 89) <|
    .splitExp 0 4
      (.step (.dropHi 4 67) <|
      .step (.xHi 65) <|
      .splitExp 1 2
        (.step (.grow 1 19) <|
        .step (.dropHi 4 56) <|
        .step (.xLo 57) <|
        .reject)
        (.step (.dropLo 4 51) <|
        .step (.xLo 53) <|
        .splitBase 3 39
          (.step (.primeHi 3 37) <|
          .step (.dropLo 4 63) <|
          .step (.xLo 65) <|
          .splitExp 2 2
            (.missing 2 19)
            (.reject))
          (.step (.primeLo 3 41) <|
          .step (.dropHi 4 57) <|
          .splitBase 3 41
            (.step (.dropLo 4 54) <|
            .step (.xLo 57) <|
            .missing 4 29)
            (.step (.primeLo 3 43) <|
            .step (.dropHi 4 53) <|
            .splitExp 2 2
              (.missing 2 19)
              (.reject)))))
      (.step (.dropLo 4 53) <|
      .splitExp 1 2
        (.step (.grow 1 19) <|
        .step (.dropHi 4 73) <|
        .step (.xLo 57) <|
        .step (.xHi 57) <|
        .missing 4 29)
        (.step (.dropLo 4 63) <|
        .step (.xLo 65) <|
        .splitBase 3 39
          (.step (.primeHi 3 37) <|
          .step (.dropLo 4 83) <|
          .step (.xLo 85) <|
          .splitExp 2 2
            (.missing 2 19)
            (.step (.dropLo 4 88) <|
            .step (.xLo 89) <|
            .missing 4 5))
          (.step (.primeLo 3 41) <|
          .step (.dropHi 4 74) <|
          .step (.xHi 73) <|
          .splitBase 3 41
            (.step (.dropLo 4 68) <|
            .step (.xLo 69) <|
            .splitExp 2 2
              (.missing 2 19)
              (.step (.dropLo 4 71) <|
              .step (.xLo 73) <|
              .missing 4 37))
            (.step (.primeLo 3 43) <|
            .step (.dropHi 4 68) <|
            .step (.xHi 65) <|
            .splitExp 2 2
              (.missing 2 19)
              (.reject))))))

theorem deficientFourPowerGeneralPart007 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,31,43,2,0⟩, ⟨true,29,181,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart007Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart008Tree : Tree :=
  .step (.primeHi 3 43) <|
  .step (.dropLo 4 27) <|
  .step (.xLo 29) <|
  .splitBase 3 29
    (.step (.dropLo 4 39) <|
    .step (.xLo 41) <|
    .splitBase 2 11
      (.use 0)
      (.step (.primeLo 2 13) <|
      .step (.dropHi 4 111) <|
      .step (.xHi 109) <|
      .splitBase 3 25
        (.step (.primeHi 3 23) <|
        .step (.dropLo 4 60) <|
        .step (.xLo 61) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 76) <|
          .step (.xLo 77) <|
          .reject)
          (.step (.dropLo 4 77) <|
          .splitExp 1 2
            (.missing 1 19)
            (.step (.dropLo 4 99) <|
            .step (.xLo 101) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.step (.dropLo 4 103) <|
              .step (.xLo 105) <|
              .splitExp 2 2
                (.missing 2 61)
                (.step (.dropLo 4 108) <|
                .step (.xLo 109) <|
                .missing 4 5)))))
        (.step (.primeLo 3 29) <|
        .step (.dropHi 4 54) <|
        .step (.xHi 53) <|
        .splitExp 0 4
          (.missing 0 11)
          (.step (.dropLo 4 45) <|
          .splitExp 1 2
            (.missing 1 19)
            (.step (.dropLo 4 52) <|
            .step (.xLo 53) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.reject))))))
    (.step (.primeLo 3 31) <|
    .step (.dropHi 4 184) <|
    .step (.xHi 181) <|
    .splitBase 2 11
      (.use 1)
      (.step (.primeLo 2 13) <|
      .step (.dropHi 4 48) <|
      .step (.xHi 45) <|
      .splitBase 3 35
        (.step (.primeHi 3 31) <|
        .step (.dropLo 4 35) <|
        .step (.xLo 37) <|
        .splitExp 0 4
          (.missing 0 11)
          (.step (.dropLo 4 41) <|
          .splitExp 1 2
            (.missing 1 19)
            (.reject)))
        (.step (.primeLo 3 37) <|
        .step (.dropHi 4 38) <|
        .step (.xHi 37) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 33) <|
          .step (.xLo 33) <|
          .missing 4 17)
          (.step (.dropLo 4 30) <|
          .step (.xLo 33) <|
          .splitExp 1 2
            (.missing 1 19)
            (.splitBase 3 39
              (.step (.primeHi 3 37) <|
              .reject)
              (.step (.primeLo 3 41) <|
              .step (.dropHi 4 35) <|
              .step (.xHi 33) <|
              .missing 4 17))))))

private def deficientFourPowerGeneralPart008Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,23,29,2,0⟩, ⟨true,41,0,5,0⟩], 1, deficientFourPowerGeneralPart006⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,31,43,2,0⟩, ⟨true,29,181,5,0⟩], 1, deficientFourPowerGeneralPart007⟩]

theorem deficientFourPowerGeneralPart008 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,23,45,2,0⟩, ⟨true,17,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart008Tree deficientFourPowerGeneralPart008Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart009Tree : Tree :=
  .step (.dropLo 4 29) <|
  .splitBase 3 61
    (.step (.dropLo 4 34) <|
    .step (.xLo 37) <|
    .splitExp 0 4
      (.step (.dropHi 4 48) <|
      .step (.xHi 45) <|
      .splitBase 3 53
        (.splitExp 1 2
          (.missing 1 19)
          (.step (.dropLo 3 48) <|
          .step (.dropLo 4 41) <|
          .step (.primeLo 3 53) <|
          .step (.dropHi 4 43) <|
          .step (.xHi 41) <|
          .reject))
        (.step (.primeLo 3 59) <|
        .step (.dropHi 4 40) <|
        .step (.xHi 37) <|
        .missing 4 19))
      (.step (.dropLo 4 39) <|
      .step (.xLo 41) <|
      .splitBase 3 53
        (.step (.dropLo 4 43) <|
        .step (.xLo 45) <|
        .splitExp 1 2
          (.step (.grow 1 19) <|
          .step (.dropHi 4 51) <|
          .step (.xLo 57) <|
          .reject)
          (.step (.dropLo 4 49) <|
          .splitBase 3 49
            (.step (.primeHi 3 47) <|
            .step (.dropLo 4 56) <|
            .step (.xLo 57) <|
            .missing 4 29)
            (.step (.primeLo 3 53) <|
            .step (.dropHi 4 52) <|
            .step (.xHi 49) <|
            .missing 4 5)))
        (.step (.primeLo 3 59) <|
        .step (.dropHi 4 47) <|
        .step (.xHi 45) <|
        .splitExp 1 2
          (.missing 1 19)
          (.step (.dropLo 4 44) <|
          .step (.xLo 45) <|
          .missing 4 23))))
    (.step (.primeLo 3 67) <|
    .step (.dropHi 4 43) <|
    .step (.xHi 41) <|
    .splitExp 0 4
      (.step (.dropHi 4 37) <|
      .splitExp 1 2
        (.missing 1 19)
        (.step (.dropLo 4 31) <|
        .step (.xLo 33) <|
        .step (.dropHi 3 86) <|
        .step (.primeHi 3 83) <|
        .splitBase 3 73
          (.step (.dropLo 4 34) <|
          .step (.xLo 37) <|
          .missing 4 19)
          (.step (.primeLo 3 79) <|
          .step (.dropHi 4 34) <|
          .step (.xHi 33) <|
          .missing 4 17)))
      (.step (.dropLo 4 32) <|
      .step (.xLo 33) <|
      .splitExp 1 2
        (.missing 1 19)
        (.step (.dropLo 3 68) <|
        .step (.dropLo 4 35) <|
        .step (.primeLo 3 71) <|
        .step (.xLo 37) <|
        .splitBase 3 77
          (.step (.primeHi 3 73) <|
          .step (.dropLo 4 39) <|
          .step (.xLo 41) <|
          .splitExp 2 2
            (.missing 2 19)
            (.splitExp 0 6
              (.missing 0 1093)
              (.reject)))
          (.step (.primeLo 3 79) <|
          .step (.dropHi 4 39) <|
          .step (.xHi 37) <|
          .missing 4 19))))

theorem deficientFourPowerGeneralPart009 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,47,89,2,0⟩, ⟨true,21,57,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart009Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
