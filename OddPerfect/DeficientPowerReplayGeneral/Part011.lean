module

public import OddPerfect.DeficientPowerReplayGeneral.Part010

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart050Tree : Tree :=
  .step (.dropLo 4 117) <|
  .splitExp 0 4
    (.step (.grow 0 11) <|
    .step (.dropHi 4 339) <|
    .step (.xLo 121) <|
    .step (.xHi 297) <|
    .splitBase 3 393
      (.step (.primeHi 3 389) <|
      .step (.dropLo 4 167) <|
      .step (.xLo 209) <|
      .step (.dropHi 3 309) <|
      .step (.primeHi 3 307) <|
      .splitBase 3 239
        (.step (.dropLo 4 229) <|
        .step (.xLo 253) <|
        .splitBase 3 215
          (.step (.primeHi 3 211) <|
          .step (.dropLo 4 262) <|
          .step (.xLo 297) <|
          .missing 4 149)
          (.step (.primeLo 3 223) <|
          .step (.dropHi 4 282) <|
          .step (.xHi 253) <|
          .missing 4 127))
        (.step (.primeLo 3 241) <|
        .step (.dropHi 4 258) <|
        .step (.xHi 253) <|
        .splitBase 3 269
          (.splitBase 3 253
            (.step (.primeHi 3 251) <|
            .step (.dropLo 4 219) <|
            .step (.xLo 253) <|
            .missing 4 127)
            (.step (.primeLo 3 257) <|
            .step (.dropHi 4 242) <|
            .step (.xHi 209) <|
            .missing 4 7))
          (.step (.primeLo 3 271) <|
          .step (.dropHi 4 230) <|
          .step (.xHi 209) <|
          .missing 4 7)))
      (.step (.primeLo 3 397) <|
      .step (.dropHi 4 181) <|
      .step (.xHi 165) <|
      .step (.dropLo 3 403) <|
      .step (.primeLo 3 409) <|
      .splitBase 3 817
        (.step (.primeHi 3 811) <|
        .step (.dropLo 4 136) <|
        .step (.xLo 165) <|
        .missing 4 83)
        (.step (.primeLo 3 821) <|
        .step (.dropHi 4 147) <|
        .step (.xHi 121) <|
        .missing 4 61)))
    (.step (.dropLo 3 204) <|
    .step (.dropLo 4 204) <|
    .step (.primeLo 3 211) <|
    .step (.xLo 205) <|
    .splitBase 3 421
      (.step (.dropLo 4 397) <|
      .splitBase 3 281
        (.use 0)
        (.step (.primeLo 3 283) <|
        .step (.dropHi 4 2673) <|
        .splitBase 3 337
          (.use 1)
          (.step (.primeLo 3 347) <|
          .step (.dropHi 4 973) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 474) <|
            .step (.xLo 477) <|
            .splitBase 3 379
              (.step (.dropLo 4 542) <|
              .step (.xLo 545) <|
              .splitExp 1 4
                (.step (.grow 1 11) <|
                .step (.grow 1 71) <|
                .step (.dropHi 4 742) <|
                .step (.xLo 781) <|
                .reject)
                (.step (.dropLo 4 650) <|
                .step (.xLo 653) <|
                .splitExp 2 2
                  (.step (.grow 2 307) <|
                  .step (.dropHi 4 812) <|
                  .step (.xLo 921) <|
                  .reject)
                  (.step (.dropLo 4 748) <|
                  .step (.xLo 749) <|
                  .splitBase 3 361
                    (.use 2)
                    (.step (.primeLo 3 367) <|
                    .step (.dropHi 4 844) <|
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
                          (.step (.dropHi 4 835) <|
                          .step (.xHi 833) <|
                          .missing 4 139)
                          (.step (.dropLo 4 839) <|
                          .step (.xLo 841) <|
                          .missing 4 421)))
                      (.step (.primeLo 3 373) <|
                      .step (.dropHi 4 813) <|
                      .splitExp 0 8
                        (.step (.grow 0 13) <|
                        .missing 0 757)
                        (.step (.dropLo 4 775) <|
                        .step (.xLo 777) <|
                        .splitBase 3 375
                          (.step (.primeHi 3 373) <|
                          .step (.dropLo 4 801) <|
                          .splitExp 1 6
                            (.step (.dropHi 4 805) <|
                            .splitExp 0 10
                              (.step (.grow 0 23) <|
                              .step (.dropHi 4 801) <|
                              .reject)
                              (.step (.dropLo 4 804) <|
                              .step (.xLo 805) <|
                              .missing 4 13))
                            (.step (.dropLo 4 809) <|
                            .splitExp 0 10
                              (.missing 0 23)
                              (.step (.dropLo 4 812) <|
                              .step (.xLo 813) <|
                              .missing 4 11)))
                          (.step (.primeLo 3 379) <|
                          .step (.dropHi 4 786) <|
                          .step (.xHi 785) <|
                          .splitExp 1 6
                            (.step (.dropHi 4 778) <|
                            .step (.xHi 777) <|
                            .missing 4 389)
                            (.step (.dropLo 4 782) <|
                            .step (.xLo 785) <|
                            .missing 4 131))))))))
              (.use 3)))))
      (.use 4))

private def deficientFourPowerGeneralPart050Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,211,281,2,0⟩, ⟨true,397,0,5,0⟩], 1, deficientFourPowerGeneralPart032⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,283,337,2,0⟩, ⟨true,397,2673,5,0⟩], 1, deficientFourPowerGeneralPart035⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,361,2,0⟩, ⟨true,749,973,5,0⟩], 1, deficientFourPowerGeneralPart036⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,380,421,2,0⟩, ⟨true,477,973,5,0⟩], 1, deficientFourPowerGeneralPart037⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,422,0,2,0⟩, ⟨true,205,0,5,0⟩], 1, deficientFourPowerGeneralPart049⟩]

theorem deficientFourPowerGeneralPart050 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,197,0,2,0⟩, ⟨true,69,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart050Tree deficientFourPowerGeneralPart050Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart051Tree : Tree :=
  .step (.primeLo 3 263) <|
  .step (.dropHi 4 150) <|
  .step (.xHi 149) <|
  .splitBase 3 313
    (.step (.dropLo 4 122) <|
    .step (.xLo 125) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 4 128) <|
      .step (.xLo 129) <|
      .splitBase 3 285
        (.step (.primeHi 3 283) <|
        .step (.dropLo 4 134) <|
        .step (.xLo 137) <|
        .splitExp 1 4
          (.missing 1 11)
          (.step (.dropLo 4 140) <|
          .step (.xLo 141) <|
          .splitBase 3 271
            (.step (.dropLo 4 143) <|
            .step (.xLo 145) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 146) <|
              .step (.xLo 149) <|
              .step (.dropHi 3 268) <|
              .step (.primeHi 3 263) <|
              .reject))
            (.step (.primeLo 3 277) <|
            .step (.dropHi 4 146) <|
            .step (.xHi 145) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 143) <|
              .step (.xLo 145) <|
              .missing 4 73))))
        (.step (.primeLo 3 293) <|
        .step (.dropHi 4 142) <|
        .step (.xHi 141) <|
        .splitExp 1 4
          (.missing 1 11)
          (.step (.dropLo 4 134) <|
          .step (.xLo 137) <|
          .splitBase 3 301
            (.step (.primeHi 3 293) <|
            .step (.dropLo 4 138) <|
            .step (.xLo 141) <|
            .missing 4 71)
            (.step (.primeLo 3 307) <|
            .step (.dropHi 4 139) <|
            .step (.xHi 137) <|
            .missing 4 23)))))
    (.step (.primeLo 3 317) <|
    .step (.dropHi 4 137) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 4 119) <|
      .step (.xLo 121) <|
      .splitBase 3 349
        (.step (.dropLo 4 123) <|
        .step (.xLo 125) <|
        .splitExp 1 4
          (.missing 1 11)
          (.step (.dropLo 4 128) <|
          .step (.xLo 129) <|
          .splitBase 3 331
            (.step (.dropLo 4 131) <|
            .step (.xLo 133) <|
            .splitExp 2 2
              (.missing 2 127)
              (.splitBase 3 323
                (.step (.primeHi 3 317) <|
                .step (.dropLo 4 136) <|
                .step (.xLo 137) <|
                .missing 4 23)
                (.step (.primeLo 3 331) <|
                .step (.dropHi 4 134) <|
                .step (.xHi 133) <|
                .missing 4 67)))
            (.step (.primeLo 3 337) <|
            .step (.dropHi 4 133) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 130) <|
              .step (.xLo 133) <|
              .missing 4 67))))
        (.step (.primeLo 3 353) <|
        .step (.dropHi 4 131) <|
        .step (.xHi 129) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .missing 1 71)
          (.step (.dropLo 4 123) <|
          .step (.xLo 125) <|
          .splitBase 3 369
            (.step (.primeHi 3 367) <|
            .step (.dropLo 4 126) <|
            .step (.xLo 129) <|
            .missing 4 13)
            (.step (.primeLo 3 373) <|
            .step (.dropHi 4 128) <|
            .step (.xHi 125) <|
            .missing 4 7)))))

theorem deficientFourPowerGeneralPart051 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,262,389,2,0⟩, ⟨true,113,185,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart051Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart052Tree : Tree :=
  .step (.primeHi 3 389) <|
  .step (.dropLo 4 113) <|
  .splitBase 3 261
    (.step (.primeHi 3 257) <|
    .step (.dropLo 4 133) <|
    .splitBase 3 223
      (.step (.dropLo 4 145) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.step (.dropLo 4 154) <|
        .step (.xLo 157) <|
        .splitBase 3 209
          (.step (.primeHi 3 199) <|
          .step (.dropLo 4 168) <|
          .step (.xLo 169) <|
          .splitExp 1 4
            (.missing 1 11)
            (.step (.dropLo 4 177) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 182) <|
              .step (.xLo 185) <|
              .missing 4 31)))
          (.step (.primeLo 3 211) <|
          .step (.dropHi 4 175) <|
          .step (.xHi 173) <|
          .splitExp 1 4
            (.step (.grow 1 11) <|
            .missing 1 71)
            (.step (.dropLo 4 162) <|
            .step (.xLo 165) <|
            .splitBase 3 215
              (.step (.primeHi 3 211) <|
              .step (.dropLo 4 169) <|
              .splitExp 2 2
                (.missing 2 127)
                (.reject))
              (.step (.primeLo 3 223) <|
              .step (.dropHi 4 167) <|
              .step (.xHi 165) <|
              .missing 4 83)))))
      (.step (.primeLo 3 227) <|
      .step (.dropHi 4 165) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.step (.dropLo 4 141) <|
        .splitBase 3 241
          (.step (.dropLo 4 146) <|
          .step (.xLo 149) <|
          .splitExp 1 4
            (.step (.grow 1 11) <|
            .missing 1 71)
            (.step (.dropLo 4 153) <|
            .splitBase 3 233
              (.step (.dropLo 4 157) <|
              .splitExp 2 2
                (.missing 2 127)
                (.step (.dropLo 4 160) <|
                .step (.xLo 161) <|
                .splitBase 3 229
                  (.step (.dropLo 4 162) <|
                  .step (.xLo 165) <|
                  .missing 4 83)
                  (.step (.primeLo 3 233) <|
                  .step (.dropHi 4 162) <|
                  .step (.xHi 161) <|
                  .splitExp 0 8
                    (.missing 0 13)
                    (.reject))))
              (.step (.primeLo 3 239) <|
              .step (.dropHi 4 159) <|
              .step (.xHi 157) <|
              .splitExp 2 2
                (.missing 2 127)
                (.reject))))
          (.step (.primeLo 3 251) <|
          .step (.dropHi 4 154) <|
          .step (.xHi 153) <|
          .splitExp 1 4
            (.missing 1 11)
            (.step (.dropLo 4 147) <|
            .step (.xLo 149) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 151) <|
              .step (.xLo 153) <|
              .missing 4 7))))))
    (.use 0)

private def deficientFourPowerGeneralPart052Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,262,389,2,0⟩, ⟨true,113,185,5,0⟩], 1, deficientFourPowerGeneralPart051⟩]

theorem deficientFourPowerGeneralPart052 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,197,393,2,0⟩, ⟨true,89,185,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart052Tree deficientFourPowerGeneralPart052Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart053Tree : Tree :=
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
          .splitBase 3 421
            (.splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 3 399) <|
              .step (.dropLo 4 123) <|
              .step (.primeLo 3 401) <|
              .step (.xLo 125) <|
              .missing 4 7))
            (.step (.primeLo 3 431) <|
            .step (.dropHi 4 123) <|
            .step (.xHi 121) <|
            .missing 4 61)))
        (.step (.primeLo 3 457) <|
        .step (.dropHi 4 121) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .missing 1 71)
          (.step (.dropLo 4 114) <|
          .step (.xLo 117) <|
          .splitBase 3 487
            (.splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 118) <|
              .step (.xLo 121) <|
              .missing 4 61))
            (.step (.primeLo 3 491) <|
            .step (.dropHi 4 119) <|
            .step (.xHi 117) <|
            .missing 4 59)))))
    (.step (.primeLo 3 541) <|
    .step (.dropHi 4 116) <|
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
          (.step (.dropLo 3 558) <|
          .step (.dropLo 4 110) <|
          .step (.primeLo 3 563) <|
          .step (.xLo 113) <|
          .step (.dropHi 3 632) <|
          .step (.primeHi 3 631) <|
          .splitExp 2 2
            (.missing 2 127)
            (.step (.dropLo 3 607) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 625) <|
              .step (.primeLo 3 631) <|
              .splitExp 1 6
                (.reject)
                (.splitExp 0 10
                  (.missing 0 23)
                  (.reject))))))
        (.step (.primeLo 3 643) <|
        .step (.dropHi 4 112) <|
        .step (.xHi 109) <|
        .splitExp 1 4
          (.missing 1 11)
          (.step (.dropLo 3 683) <|
          .step (.dropLo 4 106) <|
          .step (.xLo 109) <|
          .missing 4 11))))

theorem deficientFourPowerGeneralPart053 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,397,793,2,0⟩, ⟨true,89,125,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart053Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart054Tree : Tree :=
  .step (.primeLo 3 197) <|
  .splitBase 2 17
    (.use 0)
    (.step (.primeLo 2 19) <|
    .step (.dropHi 4 186) <|
    .step (.xHi 185) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.dropHi 4 105) <|
      .step (.xLo 77) <|
      .step (.xHi 77) <|
      .missing 4 13)
      (.step (.dropLo 4 88) <|
      .step (.xLo 89) <|
      .splitBase 3 393
        (.use 1)
        (.step (.primeLo 3 397) <|
        .step (.dropHi 4 126) <|
        .step (.xHi 125) <|
        .splitBase 3 793
          (.use 2)
          (.step (.primeLo 3 797) <|
          .step (.dropHi 4 109) <|
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
                  (.step (.dropLo 4 103) <|
                  .step (.xLo 105) <|
                  .splitBase 3 905
                    (.step (.primeHi 3 887) <|
                    .splitExp 2 2
                      (.missing 2 127)
                      (.step (.dropLo 4 106) <|
                      .step (.xLo 109) <|
                      .missing 4 11))
                    (.step (.primeLo 3 907) <|
                    .step (.dropHi 4 107) <|
                    .step (.xHi 105) <|
                    .missing 4 53))))
              (.step (.primeLo 3 1061) <|
              .step (.dropHi 4 105) <|
              .splitExp 0 6
                (.step (.fix 0 1093 3) <|
                .step (.dropLo 4 95) <|
                .step (.dropHi 4 100) <|
                .step (.xLo 97) <|
                .step (.xHi 97) <|
                .missing 4 7)
                (.step (.dropLo 4 97) <|
                .splitExp 1 4
                  (.missing 1 11)
                  (.step (.dropLo 4 100) <|
                  .step (.xLo 101) <|
                  .splitBase 3 1269
                    (.step (.primeHi 3 1259) <|
                    .splitExp 2 2
                      (.missing 2 127)
                      (.step (.dropLo 4 103) <|
                      .step (.xLo 105) <|
                      .missing 4 53))
                    (.step (.primeLo 3 1277) <|
                    .step (.dropHi 4 103) <|
                    .step (.xHi 101) <|
                    .missing 4 17)))))
            (.step (.primeLo 3 1597) <|
            .step (.dropHi 4 102) <|
            .step (.xHi 101) <|
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
                    .step (.dropHi 4 100) <|
                    .step (.xHi 97) <|
                    .missing 4 7))))
              (.step (.primeLo 3 3203) <|
              .step (.dropHi 4 98) <|
              .step (.xHi 97) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 4 91) <|
                .step (.xLo 93) <|
                .splitExp 1 4
                  (.missing 1 11)
                  (.step (.dropLo 4 94) <|
                  .step (.xLo 97) <|
                  .missing 4 7))))))))

private def deficientFourPowerGeneralPart054Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,197,0,2,0⟩, ⟨true,69,0,5,0⟩], 1, deficientFourPowerGeneralPart050⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,197,393,2,0⟩, ⟨true,89,185,5,0⟩], 1, deficientFourPowerGeneralPart052⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,397,793,2,0⟩, ⟨true,89,125,5,0⟩], 1, deficientFourPowerGeneralPart053⟩]

theorem deficientFourPowerGeneralPart054 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,194,0,2,0⟩, ⟨true,69,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart054Tree deficientFourPowerGeneralPart054Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
