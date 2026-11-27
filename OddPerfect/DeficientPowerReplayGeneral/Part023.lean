module

public import OddPerfect.DeficientPowerReplayGeneral.Part022

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart110Tree : Tree :=
  .step (.primeLo 3 1657) <|
  .splitBase 2 253
    (.step (.primeHi 2 251) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 2 236) <|
      .step (.dropLo 3 4161) <|
      .step (.primeLo 2 239) <|
      .step (.primeLo 3 4177) <|
      .splitExp 1 2
        (.missing 1 307)
        (.step (.dropLo 2 248) <|
        .step (.dropLo 3 26699) <|
        .step (.primeLo 2 251) <|
        .splitSpecial 5
          (.missing 4 7)
          (.reject))))
    (.step (.primeLo 2 257) <|
    .step (.dropHi 3 65536) <|
    .step (.primeHi 3 65521) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.splitBase 3 3231
        (.use 0)
        (.step (.primeLo 3 3251) <|
        .step (.dropHi 2 277) <|
        .splitBase 3 6193
          (.step (.primeHi 3 6173) <|
          .splitBase 2 265
            (.step (.primeHi 2 263) <|
            .splitExp 1 2
              (.missing 1 307)
              (.step (.dropLo 2 259) <|
              .step (.dropLo 3 4547) <|
              .step (.primeLo 2 263) <|
              .splitSpecial 5
                (.missing 4 7)
                (.reject)))
            (.step (.primeLo 2 269) <|
            .step (.dropHi 3 5277) <|
            .step (.primeHi 3 5273) <|
            .splitExp 1 2
              (.missing 1 307)
              (.splitBase 3 4021
                (.splitBase 2 271
                  (.splitSpecial 5
                    (.missing 4 7)
                    (.step (.dropLo 3 3722) <|
                    .step (.primeLo 3 3727) <|
                    .splitExp 0 8
                      (.missing 0 13)
                      (.reject)))
                  (.step (.primeLo 2 277) <|
                  .step (.dropHi 3 3364) <|
                  .step (.primeHi 3 3361) <|
                  .splitSpecial 5
                    (.missing 4 7)
                    (.splitExp 0 8
                      (.missing 0 13)
                      (.step (.dropLo 3 3292) <|
                      .step (.primeLo 3 3299) <|
                      .splitExp 0 10
                        (.missing 0 23)
                        (.step (.dropLo 3 3347) <|
                        .splitBase 3 3353
                          (.step (.primeHi 3 3347) <|
                          .reject)
                          (.step (.primeLo 3 3359) <|
                          .splitExp 1 4
                            (.reject)
                            (.splitExp 0 12
                              (.reject)
                              (.reject))))))))
                (.use 1))))
          (.use 2))))

private def deficientFourPowerGeneralPart110Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,293,2,0⟩, ⟨false,1657,3231,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart105⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨false,4022,5273,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart106⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,277,2,0⟩, ⟨false,6194,65521,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart109⟩]

theorem deficientFourPowerGeneralPart110 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,223,293,2,0⟩, ⟨false,1642,0,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart110Tree deficientFourPowerGeneralPart110Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart111Tree : Tree :=
  .step (.primeHi 2 293) <|
  .splitBase 3 301
    (.step (.primeHi 3 293) <|
    .step (.primeHi 2 283) <|
    .splitBase 1 17
      (.step (.dropLo 2 205) <|
      .step (.dropLo 3 210) <|
      .step (.primeLo 2 211) <|
      .step (.primeLo 3 223) <|
      .splitExp 0 4
        (.missing 0 11)
        (.reject))
      (.step (.primeLo 1 19) <|
      .step (.dropHi 2 261) <|
      .step (.dropHi 3 268) <|
      .step (.primeHi 3 263) <|
      .step (.primeHi 2 257) <|
      .splitExp 0 4
        (.missing 0 11)
        (.splitBase 2 187
          (.step (.primeHi 2 181) <|
          .step (.dropLo 3 179) <|
          .splitBase 3 213
            (.step (.primeHi 3 211) <|
            .step (.dropLo 2 157) <|
            .splitBase 3 193
              (.step (.dropLo 2 168) <|
              .step (.primeLo 2 173) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.reject))
              (.step (.primeLo 3 197) <|
              .splitBase 2 167
                (.splitExp 0 6
                  (.missing 0 1093)
                  (.reject))
                (.step (.primeLo 2 173) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.splitBase 3 203
                    (.step (.primeHi 3 199) <|
                    .step (.dropLo 2 176) <|
                    .step (.primeLo 2 179) <|
                    .splitExp 1 2
                      (.missing 1 127)
                      (.step (.dropLo 2 180) <|
                      .step (.dropLo 3 198) <|
                      .step (.primeLo 2 181) <|
                      .step (.primeLo 3 199) <|
                      .splitSpecial 5
                        (.missing 4 7)
                        (.reject)))
                    (.step (.primeLo 3 211) <|
                    .step (.dropHi 2 175) <|
                    .step (.primeHi 2 173) <|
                    .splitExp 1 2
                      (.missing 1 127)
                      (.splitSpecial 5
                        (.missing 4 7)
                        (.reject)))))))
            (.use 0))
          (.step (.primeLo 2 191) <|
          .step (.primeLo 3 193) <|
          .reject))))
    (.step (.primeLo 3 307) <|
    .step (.dropHi 1 18) <|
    .step (.primeHi 1 17) <|
    .splitExp 0 4
      (.missing 0 11)
      (.step (.dropLo 2 216) <|
      .step (.dropLo 3 820) <|
      .step (.primeLo 2 223) <|
      .step (.primeLo 3 821) <|
      .splitBase 3 1641
        (.step (.primeHi 3 1637) <|
        .step (.dropLo 2 248) <|
        .step (.primeLo 2 251) <|
        .splitExp 0 6
          (.step (.fix 0 1093 3) <|
          .step (.dropLo 2 269) <|
          .step (.dropHi 2 289) <|
          .step (.primeHi 2 283) <|
          .splitExp 1 2
            (.missing 1 307)
            (.reject))
          (.step (.dropLo 2 276) <|
          .step (.dropLo 3 1229) <|
          .step (.primeLo 2 277) <|
          .splitExp 1 2
            (.missing 1 307)
            (.reject)))
        (.use 1)))

private def deficientFourPowerGeneralPart111Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,149,181,2,0⟩, ⟨false,214,263,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart103⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,223,293,2,0⟩, ⟨false,1642,0,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart110⟩]

theorem deficientFourPowerGeneralPart111 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,149,297,2,0⟩, ⟨false,151,0,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart111Tree deficientFourPowerGeneralPart111Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart112Tree : Tree :=
  .step (.primeLo 3 571) <|
  .step (.dropHi 2 463) <|
  .splitBase 2 451
    (.step (.primeHi 2 449) <|
    .splitBase 3 585
      (.step (.primeHi 3 577) <|
      .splitSpecial 5
        (.missing 4 7)
        (.step (.dropLo 2 448) <|
        .step (.dropLo 3 576) <|
        .step (.primeLo 2 449) <|
        .step (.primeLo 3 577) <|
        .splitExp 0 8
          (.missing 0 13)
          (.reject)))
      (.step (.primeLo 3 587) <|
      .splitSpecial 5
        (.missing 4 7)
        (.splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 3 591) <|
          .step (.primeLo 3 593) <|
          .splitBase 2 445
            (.step (.primeHi 2 443) <|
            .reject)
            (.step (.primeLo 2 449) <|
            .step (.dropHi 3 594) <|
            .step (.primeHi 3 593) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject))))))
    (.step (.primeLo 2 457) <|
    .step (.dropHi 3 580) <|
    .step (.primeHi 3 577) <|
    .splitSpecial 5
      (.missing 4 7)
      (.splitExp 0 8
        (.missing 0 13)
        (.step (.dropLo 2 458) <|
        .step (.primeLo 2 461) <|
        .step (.dropHi 3 574) <|
        .step (.primeHi 3 571) <|
        .splitBase 2 461
          (.reject)
          (.step (.primeLo 2 463) <|
          .splitExp 0 10
            (.missing 0 23)
            (.splitExp 1 4
              (.splitExp 0 12
                (.reject)
                (.reject))
              (.reject))))))

theorem deficientFourPowerGeneralPart112 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,443,479,2,0⟩, ⟨false,570,601,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart112Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart113Tree : Tree :=
  .step (.primeLo 3 541) <|
  .step (.dropHi 2 485) <|
  .step (.primeHi 2 479) <|
  .splitBase 2 441
    (.step (.primeHi 2 439) <|
    .splitExp 1 2
      (.missing 1 307)
      (.step (.dropLo 2 420) <|
      .step (.dropLo 3 572) <|
      .step (.primeLo 2 421) <|
      .step (.primeLo 3 577) <|
      .splitBase 2 429
        (.step (.primeHi 2 421) <|
        .step (.dropLo 3 606) <|
        .step (.primeLo 3 607) <|
        .splitSpecial 5
          (.missing 4 7)
          (.reject))
        (.step (.primeLo 2 431) <|
        .splitBase 3 591
          (.step (.primeHi 3 587) <|
          .splitSpecial 5
            (.missing 4 7)
            (.reject))
          (.step (.primeLo 3 593) <|
          .splitSpecial 5
            (.missing 4 7)
            (.step (.dropLo 2 432) <|
            .step (.primeLo 2 433) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject))))))
    (.step (.primeLo 2 443) <|
    .step (.dropHi 3 605) <|
    .step (.primeHi 3 601) <|
    .splitExp 1 2
      (.missing 1 307)
      (.splitBase 3 569
        (.splitBase 2 459
          (.step (.primeHi 2 457) <|
          .step (.dropLo 3 544) <|
          .step (.primeLo 3 547) <|
          .splitSpecial 5
            (.missing 4 7)
            (.step (.dropLo 2 453) <|
            .step (.dropLo 3 563) <|
            .step (.primeLo 2 457) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject)))
          (.step (.primeLo 2 461) <|
          .splitBase 3 553
            (.step (.primeHi 3 547) <|
            .splitSpecial 5
              (.missing 4 7)
              (.step (.dropLo 2 468) <|
              .step (.primeLo 2 479) <|
              .splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 3 546) <|
                .step (.primeLo 3 547) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.reject))))
            (.step (.primeLo 3 557) <|
            .step (.dropHi 2 472) <|
            .step (.primeHi 2 467) <|
            .splitSpecial 5
              (.missing 4 7)
              (.splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 2 463) <|
                .step (.dropLo 3 563) <|
                .splitBase 3 565
                  (.step (.primeHi 3 563) <|
                  .reject)
                  (.step (.primeLo 3 569) <|
                  .step (.dropHi 2 464) <|
                  .step (.primeHi 2 463) <|
                  .reject))))))
        (.use 0)))

private def deficientFourPowerGeneralPart113Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,443,479,2,0⟩, ⟨false,570,601,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart112⟩]

theorem deficientFourPowerGeneralPart113 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,17,17,2,0⟩, ⟨false,409,503,2,0⟩, ⟨false,528,607,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart113Tree deficientFourPowerGeneralPart113Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart114Tree : Tree :=
  .step (.primeLo 3 709) <|
  .step (.dropHi 2 400) <|
  .step (.primeHi 2 397) <|
  .splitExp 1 2
    (.missing 1 307)
    (.splitBase 3 767
      (.step (.primeHi 3 761) <|
      .step (.dropLo 2 368) <|
      .step (.primeLo 2 373) <|
      .splitBase 2 383
        (.splitBase 3 733
          (.step (.dropLo 2 375) <|
          .step (.primeLo 2 379) <|
          .splitSpecial 5
            (.missing 4 7)
            (.reject))
          (.step (.primeLo 3 739) <|
          .splitSpecial 5
            (.missing 4 7)
            (.step (.dropLo 2 377) <|
            .step (.dropLo 3 740) <|
            .step (.primeLo 2 379) <|
            .step (.primeLo 3 743) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject))))
        (.step (.primeLo 2 389) <|
        .step (.dropHi 3 746) <|
        .step (.primeHi 3 743) <|
        .splitSpecial 5
          (.missing 4 7)
          (.splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 3 715) <|
            .step (.primeLo 3 719) <|
            .step (.dropHi 2 396) <|
            .step (.primeHi 2 389) <|
            .reject))))
      (.step (.primeLo 3 769) <|
      .step (.dropHi 2 383) <|
      .splitBase 2 373
        (.splitBase 3 801
          (.step (.primeHi 3 797) <|
          .splitSpecial 5
            (.missing 4 7)
            (.step (.dropLo 2 369) <|
            .step (.dropLo 3 781) <|
            .step (.primeLo 2 373) <|
            .step (.primeLo 3 787) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject)))
          (.step (.primeLo 3 809) <|
          .splitSpecial 5
            (.missing 4 7)
            (.splitExp 0 8
              (.missing 0 13)
              (.splitBase 3 823
                (.step (.dropLo 2 370) <|
                .step (.primeLo 2 373) <|
                .step (.dropHi 3 813) <|
                .step (.primeHi 3 811) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.reject))
                (.step (.primeLo 3 827) <|
                .step (.dropHi 2 370) <|
                .step (.primeHi 2 367) <|
                .reject)))))
        (.step (.primeLo 2 379) <|
        .step (.dropHi 3 786) <|
        .step (.primeHi 3 773) <|
        .splitSpecial 5
          (.missing 4 7)
          (.splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 2 381) <|
            .step (.primeLo 2 383) <|
            .step (.dropHi 3 770) <|
            .step (.primeHi 3 769) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject))))))

theorem deficientFourPowerGeneralPart114 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,17,17,2,0⟩, ⟨false,367,433,2,0⟩, ⟨false,708,839,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart114Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
