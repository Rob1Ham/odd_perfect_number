module

public import OddPerfect.DeficientPowerReplayGeneral.Part024

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart120Tree : Tree :=
  .step (.primeLo 2 149) <|
  .step (.primeLo 3 151) <|
  .splitBase 2 297
    (.use 0)
    (.step (.primeLo 2 307) <|
    .step (.primeLo 3 311) <|
    .step (.dropHi 1 17) <|
    .step (.dropHi 2 1442) <|
    .step (.dropHi 3 1536) <|
    .step (.primeHi 3 1531) <|
    .step (.primeHi 2 1439) <|
    .splitExp 0 4
      (.missing 0 11)
      (.splitBase 2 505
        (.step (.primeHi 2 503) <|
        .step (.dropLo 3 378) <|
        .step (.primeLo 3 379) <|
        .splitBase 3 607
          (.step (.dropLo 2 334) <|
          .step (.primeLo 2 337) <|
          .splitBase 3 465
            (.step (.primeHi 3 463) <|
            .step (.primeHi 2 461) <|
            .step (.dropLo 2 404) <|
            .step (.dropLo 3 405) <|
            .step (.primeLo 2 409) <|
            .step (.primeLo 3 419) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.reject))
            (.step (.primeLo 3 467) <|
            .splitBase 2 403
              (.step (.primeHi 2 401) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 2 387) <|
                .step (.dropLo 3 576) <|
                .step (.primeLo 2 389) <|
                .step (.primeLo 3 577) <|
                .splitExp 1 2
                  (.missing 1 307)
                  (.reject)))
              (.step (.primeLo 2 409) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.splitBase 3 527
                  (.step (.primeHi 3 523) <|
                  .step (.dropLo 2 431) <|
                  .splitBase 2 463
                    (.step (.dropLo 3 483) <|
                    .step (.primeLo 3 487) <|
                    .splitExp 1 2
                      (.missing 1 307)
                      (.reject))
                    (.step (.primeLo 2 467) <|
                    .step (.primeLo 3 479) <|
                    .splitExp 1 2
                      (.missing 1 307)
                      (.step (.dropLo 2 473) <|
                      .step (.dropLo 3 490) <|
                      .step (.primeLo 2 479) <|
                      .step (.primeLo 3 491) <|
                      .splitBase 3 505
                        (.step (.primeHi 3 503) <|
                        .step (.primeHi 2 499) <|
                        .step (.dropLo 2 490) <|
                        .step (.dropLo 3 494) <|
                        .step (.primeLo 2 491) <|
                        .step (.primeLo 3 499) <|
                        .splitSpecial 5
                          (.missing 4 7)
                          (.reject))
                        (.step (.primeLo 3 509) <|
                        .splitBase 2 489
                          (.step (.primeHi 2 487) <|
                          .splitSpecial 5
                            (.missing 4 7)
                            (.reject))
                          (.step (.primeLo 2 491) <|
                          .splitSpecial 5
                            (.missing 4 7)
                            (.splitExp 0 8
                              (.missing 0 13)
                              (.step (.dropLo 2 498) <|
                              .step (.dropLo 3 518) <|
                              .step (.primeLo 2 499) <|
                              .step (.primeLo 3 521) <|
                              .step (.dropHi 2 502) <|
                              .step (.primeHi 2 499) <|
                              .step (.dropLo 3 522) <|
                              .step (.primeLo 3 523) <|
                              .splitExp 0 10
                                (.missing 0 23)
                                (.reject))))))))
                  (.use 1)))))
          (.use 2))
        (.step (.primeLo 2 509) <|
        .step (.primeLo 3 521) <|
        .reject)))

private def deficientFourPowerGeneralPart120Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,149,297,2,0⟩, ⟨false,151,0,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart111⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,17,17,2,0⟩, ⟨false,409,503,2,0⟩, ⟨false,528,607,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart113⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,307,503,2,0⟩, ⟨false,608,1531,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart119⟩]

theorem deficientFourPowerGeneralPart120 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,142,0,2,0⟩, ⟨false,73,0,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart120Tree deficientFourPowerGeneralPart120Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart121Tree : Tree :=
  .step (.primeLo 2 29) <|
  .step (.primeLo 3 31) <|
  .step (.dropHi 4 8) <|
  .step (.xHi 5) <|
  .splitExp 0 2
    (.step (.fix 0 13 1) <|
    .step (.dropLo 2 44) <|
    .step (.dropLo 3 44) <|
    .step (.primeLo 2 47) <|
    .step (.primeLo 3 53) <|
    .step (.dropHi 2 314) <|
    .step (.dropHi 3 1370) <|
    .step (.primeHi 3 1367) <|
    .step (.primeHi 2 313) <|
    .splitBase 3 101
      (.step (.primeHi 2 97) <|
      .step (.dropLo 2 78) <|
      .step (.dropLo 3 81) <|
      .step (.primeLo 2 79) <|
      .step (.primeLo 3 83) <|
      .splitBase 2 87
        (.step (.primeHi 2 83) <|
        .step (.dropLo 3 94) <|
        .step (.primeLo 3 97) <|
        .splitBase 2 79
          (.step (.dropLo 3 100) <|
          .step (.primeLo 3 101) <|
          .splitExp 1 2
            (.missing 1 61)
            (.reject))
          (.step (.primeLo 2 83) <|
          .step (.dropHi 3 99) <|
          .step (.primeHi 3 97) <|
          .splitExp 1 2
            (.missing 1 61)
            (.reject)))
        (.step (.primeLo 2 89) <|
        .step (.primeLo 3 97) <|
        .reject))
      (.step (.primeLo 3 103) <|
      .step (.dropHi 2 80) <|
      .step (.primeHi 2 79) <|
      .splitBase 3 191
        (.use 0)
        (.step (.primeLo 3 193) <|
        .step (.dropHi 2 59) <|
        .splitBase 3 337
          (.step (.dropLo 2 51) <|
          .step (.primeLo 2 53) <|
          .step (.dropHi 3 314) <|
          .step (.primeHi 3 313) <|
          .splitBase 3 237
            (.step (.primeHi 3 233) <|
            .step (.dropLo 2 54) <|
            .step (.primeLo 2 59) <|
            .step (.dropHi 3 194) <|
            .step (.primeHi 3 193) <|
            .splitExp 1 2
              (.missing 1 61)
              (.splitSpecial 5
                (.missing 4 7)
                (.reject)))
            (.step (.primeLo 3 239) <|
            .step (.dropHi 2 55) <|
            .step (.primeHi 2 53) <|
            .step (.dropLo 3 269) <|
            .splitExp 1 2
              (.missing 1 61)
              (.step (.dropLo 3 307) <|
              .splitSpecial 5
                (.missing 4 7)
                (.reject))))
          (.step (.primeLo 3 347) <|
          .step (.dropHi 2 52) <|
          .step (.primeHi 2 47) <|
          .step (.dropLo 3 794) <|
          .step (.primeLo 3 797) <|
          .splitExp 1 2
            (.missing 1 61)
            (.step (.dropLo 3 1240) <|
            .step (.primeLo 3 1249) <|
            .splitSpecial 5
              (.missing 4 7)
              (.step (.dropLo 3 1347) <|
              .step (.primeLo 3 1361) <|
              .splitExp 2 2
                (.missing 2 37)
                (.step (.dropLo 3 1365) <|
                .step (.primeLo 3 1367) <|
                .splitExp 1 4
                  (.reject)
                  (.reject))))))))
    (.step (.dropLo 1 15) <|
    .step (.dropLo 2 68) <|
    .step (.dropLo 3 68) <|
    .step (.primeLo 1 17) <|
    .step (.primeLo 2 71) <|
    .step (.primeLo 3 73) <|
    .splitBase 2 141
      (.step (.primeHi 2 139) <|
      .step (.dropLo 3 132) <|
      .step (.primeLo 3 137) <|
      .splitBase 3 273
        (.step (.primeHi 3 271) <|
        .step (.dropLo 2 90) <|
        .step (.primeLo 2 97) <|
        .splitBase 1 17
          (.reject)
          (.step (.primeLo 1 19) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 2 134) <|
            .step (.dropLo 3 255) <|
            .step (.primeLo 2 137) <|
            .step (.primeLo 3 257) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.reject))))
        (.use 1))
      (.use 2))

private def deficientFourPowerGeneralPart121Refs : List Known := [
  ⟨#v[⟨false,3,3,2,2⟩, ⟨false,13,13,2,0⟩, ⟨false,47,79,2,0⟩, ⟨false,103,191,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart095⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,71,139,2,0⟩, ⟨false,274,0,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart102⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,142,0,2,0⟩, ⟨false,73,0,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart120⟩]

theorem deficientFourPowerGeneralPart121 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,11,19,2,0⟩, ⟨false,26,0,2,0⟩, ⟨false,17,0,2,0⟩, ⟨true,5,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart121Tree deficientFourPowerGeneralPart121Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart122Tree : Tree :=
  .step (.primeLo 3 167) <|
  .splitBase 1 25
    (.step (.primeHi 1 23) <|
    .step (.dropLo 3 188) <|
    .step (.primeLo 3 191) <|
    .splitBase 2 45
      (.step (.primeHi 2 43) <|
      .step (.dropLo 3 1192) <|
      .step (.primeLo 3 1193) <|
      .splitExp 0 4
        (.missing 0 11)
        (.reject))
      (.step (.primeLo 2 47) <|
      .splitExp 0 4
        (.missing 0 11)
        (.step (.dropLo 2 48) <|
        .step (.dropLo 3 606) <|
        .step (.primeLo 2 53) <|
        .step (.primeLo 3 607) <|
        .step (.dropHi 3 963) <|
        .step (.primeHi 3 953) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 3 805) <|
          .step (.primeLo 3 809) <|
          .splitBase 3 875
            (.step (.primeHi 3 863) <|
            .splitExp 1 2
              (.missing 1 7)
              (.step (.dropLo 3 862) <|
              .step (.primeLo 3 863) <|
              .splitSpecial 5
                (.missing 4 7)
                (.reject)))
            (.step (.primeLo 3 877) <|
            .splitExp 1 2
              (.missing 1 7)
              (.splitBase 3 913
                (.step (.primeHi 3 911) <|
                .splitSpecial 5
                  (.missing 4 7)
                  (.reject))
                (.step (.primeLo 3 919) <|
                .splitSpecial 5
                  (.missing 4 7)
                  (.splitExp 0 8
                    (.missing 0 13)
                    (.step (.dropLo 3 951) <|
                    .step (.primeLo 3 953) <|
                    .splitExp 2 2
                      (.missing 2 7)
                      (.reject))))))))))
    (.step (.primeLo 1 29) <|
    .step (.dropHi 2 43) <|
    .step (.dropHi 3 210) <|
    .step (.primeHi 3 199) <|
    .splitExp 0 4
      (.missing 0 11)
      (.splitBase 2 41
        (.step (.dropLo 3 188) <|
        .step (.primeLo 3 191) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.reject))
        (.step (.primeLo 2 43) <|
        .step (.dropHi 3 169) <|
        .step (.primeHi 3 167) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.splitSpecial 5
            (.missing 4 7)
            (.splitExp 0 8
              (.missing 0 13)
              (.reject))))))

theorem deficientFourPowerGeneralPart122 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,23,29,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,166,0,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart122Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart123Tree : Tree :=
  .step (.dropLo 2 30) <|
  .step (.primeLo 2 31) <|
  .splitBase 2 39
    (.step (.primeHi 2 37) <|
    .step (.dropLo 1 24) <|
    .step (.dropLo 3 159) <|
    .step (.primeLo 1 29) <|
    .step (.primeLo 3 163) <|
    .splitBase 3 325
      (.step (.primeHi 3 317) <|
      .step (.dropLo 2 33) <|
      .step (.primeLo 2 37) <|
      .splitExp 0 4
        (.missing 0 11)
        (.reject))
      (.step (.primeLo 3 331) <|
      .splitExp 0 4
        (.missing 0 11)
        (.step (.dropLo 2 33) <|
        .step (.dropLo 3 380) <|
        .step (.primeLo 2 37) <|
        .step (.primeLo 3 383) <|
        .step (.dropHi 3 488) <|
        .step (.primeHi 3 487) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 3 450) <|
          .step (.primeLo 3 457) <|
          .splitBase 3 471
            (.step (.primeHi 3 467) <|
            .splitSpecial 5
              (.missing 4 7)
              (.step (.dropLo 3 463) <|
              .splitExp 0 8
                (.missing 0 13)
                (.reject)))
            (.step (.primeLo 3 479) <|
            .splitSpecial 5
              (.missing 4 7)
              (.splitExp 0 8
                (.missing 0 13)
                (.splitExp 1 2
                  (.missing 1 13)
                  (.step (.dropLo 3 482) <|
                  .step (.primeLo 3 487) <|
                  .splitExp 2 2
                    (.missing 2 7)
                    (.reject)))))))))
    (.step (.primeLo 2 41) <|
    .splitBase 3 165
      (.step (.primeHi 3 163) <|
      .splitBase 1 25
        (.step (.primeHi 1 23) <|
        .reject)
        (.step (.primeLo 1 29) <|
        .splitBase 3 109
          (.splitBase 2 45
            (.step (.primeHi 2 43) <|
            .step (.dropLo 3 98) <|
            .step (.primeLo 3 101) <|
            .splitExp 0 4
              (.missing 0 11)
              (.reject))
            (.step (.primeLo 2 47) <|
            .splitExp 0 4
              (.missing 0 11)
              (.step (.dropLo 2 48) <|
              .step (.dropLo 3 91) <|
              .step (.primeLo 2 53) <|
              .step (.primeLo 3 97) <|
              .reject)))
          (.step (.primeLo 3 113) <|
          .step (.dropHi 2 49) <|
          .step (.primeHi 2 47) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 2 42) <|
            .step (.dropLo 3 117) <|
            .step (.primeLo 2 43) <|
            .step (.primeLo 3 127) <|
            .step (.dropHi 2 46) <|
            .step (.primeHi 2 43) <|
            .step (.dropLo 3 154) <|
            .step (.primeLo 3 157) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.reject)))))
      (.use 0))

private def deficientFourPowerGeneralPart123Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,23,29,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,166,0,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart122⟩]

theorem deficientFourPowerGeneralPart123 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,23,29,2,0⟩, ⟨false,29,53,2,0⟩, ⟨false,83,0,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart123Tree deficientFourPowerGeneralPart123Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart124Tree : Tree :=
  .step (.primeLo 3 83) <|
  .splitBase 1 29
    (.use 0)
    (.step (.primeLo 1 31) <|
    .step (.primeLo 2 37) <|
    .step (.dropHi 1 40) <|
    .step (.dropHi 2 51) <|
    .step (.dropHi 3 230) <|
    .step (.primeHi 3 229) <|
    .step (.primeHi 2 47) <|
    .step (.primeHi 1 37) <|
    .splitBase 3 121
      (.step (.primeHi 3 113) <|
      .splitBase 2 41
        (.splitExp 0 4
          (.missing 0 11)
          (.step (.dropLo 1 32) <|
          .step (.primeLo 1 37) <|
          .step (.primeLo 2 41) <|
          .reject))
        (.step (.primeLo 2 43) <|
        .step (.dropHi 1 35) <|
        .step (.primeHi 1 31) <|
        .splitExp 0 4
          (.missing 0 11)
          (.step (.dropLo 3 93) <|
          .step (.primeLo 3 97) <|
          .splitBase 2 43
            (.reject)
            (.step (.primeLo 2 47) <|
            .step (.dropHi 3 98) <|
            .step (.primeHi 3 97) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.splitSpecial 5
                (.missing 4 7)
                (.reject))))))
      (.step (.primeLo 3 127) <|
      .step (.dropHi 1 34) <|
      .step (.dropHi 2 42) <|
      .step (.primeHi 2 41) <|
      .step (.primeHi 1 31) <|
      .splitExp 0 4
        (.missing 0 11)
        (.step (.dropLo 3 131) <|
        .splitBase 3 165
          (.step (.primeHi 3 163) <|
          .step (.dropLo 2 38) <|
          .step (.primeLo 2 41) <|
          .step (.dropHi 3 142) <|
          .step (.primeHi 3 139) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.reject))
          (.step (.primeLo 3 167) <|
          .step (.dropHi 2 39) <|
          .step (.primeHi 2 37) <|
          .step (.dropLo 3 203) <|
          .step (.primeLo 3 211) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 3 221) <|
            .step (.primeLo 3 223) <|
            .splitBase 3 225
              (.step (.primeHi 3 223) <|
              .splitSpecial 5
                (.missing 4 7)
                (.reject))
              (.step (.primeLo 3 227) <|
              .splitSpecial 5
                (.missing 4 7)
                (.splitExp 0 8
                  (.missing 0 13)
                  (.splitExp 1 2
                    (.missing 1 331)
                    (.reject)))))))))

private def deficientFourPowerGeneralPart124Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,23,29,2,0⟩, ⟨false,29,53,2,0⟩, ⟨false,83,0,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart123⟩]

theorem deficientFourPowerGeneralPart124 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,23,43,2,0⟩, ⟨false,29,53,2,0⟩, ⟨false,82,0,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart124Tree deficientFourPowerGeneralPart124Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
