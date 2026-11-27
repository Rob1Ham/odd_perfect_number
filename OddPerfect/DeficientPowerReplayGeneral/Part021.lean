module

public import OddPerfect.DeficientPowerReplayGeneral.Part020

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart100Tree : Tree :=
  .step (.primeLo 3 4649) <|
  .splitExp 1 2
    (.missing 1 127)
    (.splitBase 3 6177
      (.step (.primeHi 3 6173) <|
      .splitSpecial 5
        (.missing 4 7)
        (.reject))
      (.step (.primeLo 3 6197) <|
      .splitSpecial 5
        (.missing 4 7)
        (.step (.dropLo 3 6214) <|
        .step (.primeLo 3 6217) <|
        .splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 3 8639) <|
          .step (.primeLo 3 8641) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 3 9030) <|
            .step (.primeLo 3 9041) <|
            .splitBase 3 9123
              (.step (.primeHi 3 9109) <|
              .splitExp 2 2
                (.splitExp 0 12
                  (.step (.dropHi 3 9071) <|
                  .step (.primeHi 3 9067) <|
                  .splitExp 1 4
                    (.missing 1 151)
                    (.step (.dropLo 3 9063) <|
                    .step (.primeLo 3 9067) <|
                    .splitSpecial 9
                      (.missing 4 11)
                      (.reject)))
                  (.step (.dropLo 3 9076) <|
                  .step (.primeLo 3 9091) <|
                  .splitExp 1 4
                    (.missing 1 151)
                    (.reject)))
                (.reject))
              (.step (.primeLo 3 9127) <|
              .splitExp 2 2
                (.reject)
                (.splitBase 3 9167
                  (.step (.primeHi 3 9161) <|
                  .splitExp 0 12
                    (.splitExp 1 4
                      (.missing 1 151)
                      (.step (.dropLo 3 9154) <|
                      .step (.primeLo 3 9157) <|
                      .splitSpecial 9
                        (.missing 4 11)
                        (.reject)))
                    (.reject))
                  (.step (.primeLo 3 9173) <|
                  .splitExp 0 12
                    (.reject)
                    (.splitExp 1 4
                      (.missing 1 151)
                      (.step (.dropLo 3 9201) <|
                      .step (.primeLo 3 9203) <|
                      .splitSpecial 9
                        (.missing 4 11)
                        (.reject)))))))))))

theorem deficientFourPowerGeneralPart100 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,97,2,0⟩, ⟨false,4648,9209,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart100Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart101Tree : Tree :=
  .step (.primeLo 3 1031) <|
  .step (.dropHi 2 105) <|
  .step (.primeHi 2 103) <|
  .splitBase 3 1853
    (.use 0)
    (.step (.primeLo 3 1861) <|
    .step (.dropHi 2 101) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.splitBase 3 3095
        (.step (.primeHi 3 3089) <|
        .splitBase 2 97
          (.step (.dropLo 3 2701) <|
          .step (.primeLo 3 2707) <|
          .splitExp 1 2
            (.missing 1 127)
            (.reject))
          (.step (.primeLo 2 101) <|
          .step (.dropHi 3 1920) <|
          .step (.primeHi 3 1913) <|
          .splitExp 1 2
            (.missing 1 127)
            (.splitSpecial 5
              (.missing 4 7)
              (.splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 3 1894) <|
                .step (.primeLo 3 1901) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 3 1912) <|
                  .step (.primeLo 3 1913) <|
                  .splitExp 2 2
                    (.splitExp 0 12
                      (.splitExp 1 4
                        (.missing 1 151)
                        (.reject))
                      (.reject))
                    (.reject)))))))
        (.step (.primeLo 3 3109) <|
        .step (.dropHi 2 99) <|
        .step (.primeHi 2 97) <|
        .splitBase 3 4647
          (.step (.primeHi 3 4643) <|
          .splitExp 1 2
            (.missing 1 127)
            (.step (.dropLo 3 4448) <|
            .step (.primeLo 3 4451) <|
            .splitSpecial 5
              (.missing 4 7)
              (.reject)))
          (.use 1))))

private def deficientFourPowerGeneralPart101Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,103,2,0⟩, ⟨false,1031,1853,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart099⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,97,2,0⟩, ⟨false,4648,9209,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart100⟩]

theorem deficientFourPowerGeneralPart101 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,113,2,0⟩, ⟨false,1022,9209,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart101Tree deficientFourPowerGeneralPart101Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart102Tree : Tree :=
  .step (.primeLo 3 277) <|
  .splitBase 2 93
    (.step (.primeHi 2 89) <|
    .step (.dropLo 3 285) <|
    .step (.primeLo 3 293) <|
    .splitBase 1 17
      (.reject)
      (.step (.primeLo 1 19) <|
      .splitExp 0 4
        (.missing 0 11)
        (.reject)))
    (.step (.primeLo 2 97) <|
    .splitBase 1 17
      (.step (.dropLo 2 120) <|
      .step (.dropLo 3 921) <|
      .step (.primeLo 2 127) <|
      .step (.primeLo 3 929) <|
      .splitExp 0 4
        (.missing 0 11)
        (.reject))
      (.step (.primeLo 1 19) <|
      .step (.dropHi 3 9216) <|
      .step (.primeHi 3 9209) <|
      .splitExp 0 4
        (.missing 0 11)
        (.splitBase 3 537
          (.use 0)
          (.step (.primeLo 3 541) <|
          .step (.dropHi 2 116) <|
          .step (.primeHi 2 113) <|
          .splitBase 3 1021
            (.step (.dropLo 2 98) <|
            .step (.primeLo 2 101) <|
            .splitBase 2 105
              (.step (.primeHi 2 103) <|
              .step (.dropLo 3 723) <|
              .step (.primeLo 3 727) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.reject))
              (.step (.primeLo 2 107) <|
              .step (.dropHi 3 925) <|
              .step (.primeHi 3 919) <|
              .splitBase 3 681
                (.step (.primeHi 3 677) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.step (.dropLo 2 108) <|
                  .step (.dropLo 3 542) <|
                  .step (.primeLo 2 109) <|
                  .step (.primeLo 3 547) <|
                  .splitBase 3 605
                    (.step (.primeHi 3 601) <|
                    .step (.dropLo 2 110) <|
                    .step (.primeLo 2 113) <|
                    .splitExp 1 2
                      (.missing 1 127)
                      (.step (.dropLo 3 589) <|
                      .step (.primeLo 3 593) <|
                      .splitSpecial 5
                        (.missing 4 7)
                        (.reject)))
                    (.step (.primeLo 3 607) <|
                    .splitBase 2 109
                      (.step (.dropLo 3 660) <|
                      .step (.primeLo 3 661) <|
                      .splitExp 1 2
                        (.missing 1 127)
                        (.reject))
                      (.step (.primeLo 2 113) <|
                      .step (.dropHi 3 632) <|
                      .step (.primeHi 3 631) <|
                      .splitExp 1 2
                        (.missing 1 127)
                        (.splitSpecial 5
                          (.missing 4 7)
                          (.step (.dropLo 3 612) <|
                          .step (.primeLo 3 613) <|
                          .splitExp 0 8
                            (.missing 0 13)
                            (.step (.dropLo 3 629) <|
                            .step (.primeLo 3 631) <|
                            .splitExp 0 10
                              (.missing 0 23)
                              (.reject))))))))
                (.use 1)))
            (.use 2)))))

private def deficientFourPowerGeneralPart102Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,139,2,0⟩, ⟨false,277,537,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart097⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,107,113,2,0⟩, ⟨false,682,919,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart098⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,113,2,0⟩, ⟨false,1022,9209,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart101⟩]

theorem deficientFourPowerGeneralPart102 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,71,139,2,0⟩, ⟨false,274,0,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart102Tree deficientFourPowerGeneralPart102Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart103Tree : Tree :=
  .step (.primeLo 3 223) <|
  .step (.dropHi 2 167) <|
  .splitBase 2 157
    (.splitBase 3 241
      (.splitExp 0 6
        (.missing 0 1093)
        (.step (.dropLo 2 152) <|
        .step (.dropLo 3 230) <|
        .step (.primeLo 2 157) <|
        .step (.primeLo 3 233) <|
        .splitExp 1 2
          (.missing 1 127)
          (.step (.dropLo 3 238) <|
          .step (.primeLo 3 239) <|
          .splitSpecial 5
            (.missing 4 7)
            (.reject))))
      (.step (.primeLo 3 251) <|
      .step (.dropHi 2 154) <|
      .step (.primeHi 2 151) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.splitExp 1 2
          (.missing 1 127)
          (.step (.dropLo 3 254) <|
          .step (.primeLo 3 257) <|
          .splitBase 2 149
            (.step (.dropLo 3 260) <|
            .step (.primeLo 3 263) <|
            .splitSpecial 5
              (.missing 4 7)
              (.reject))
            (.step (.primeLo 2 151) <|
            .step (.dropHi 3 261) <|
            .step (.primeHi 3 257) <|
            .splitSpecial 5
              (.missing 4 7)
              (.reject))))))
    (.step (.primeLo 2 163) <|
    .step (.dropHi 3 232) <|
    .step (.primeHi 3 229) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.splitExp 1 2
        (.missing 1 127)
        (.splitBase 2 163
          (.step (.dropLo 3 226) <|
          .step (.primeLo 3 227) <|
          .splitSpecial 5
            (.missing 4 7)
            (.reject))
          (.step (.primeLo 2 167) <|
          .step (.dropHi 3 224) <|
          .step (.primeHi 3 223) <|
          .splitSpecial 5
            (.missing 4 7)
            (.splitExp 0 8
              (.missing 0 13)
              (.reject))))))

theorem deficientFourPowerGeneralPart103 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,19,19,2,0⟩, ⟨false,149,181,2,0⟩, ⟨false,214,263,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart103Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart104Tree : Tree :=
  .step (.primeLo 3 2203) <|
  .step (.dropHi 2 289) <|
  .step (.primeHi 2 283) <|
  .splitExp 1 2
    (.missing 1 307)
    (.splitBase 3 2619
      (.step (.primeHi 3 2617) <|
      .splitSpecial 5
        (.missing 4 7)
        (.step (.dropLo 2 279) <|
        .step (.dropLo 3 2349) <|
        .step (.primeLo 2 281) <|
        .step (.primeLo 3 2351) <|
        .splitExp 0 8
          (.missing 0 13)
          (.reject)))
      (.step (.primeLo 3 2621) <|
      .splitSpecial 5
        (.missing 4 7)
        (.splitBase 2 279
          (.step (.primeHi 2 277) <|
          .step (.dropLo 3 2866) <|
          .step (.primeLo 3 2879) <|
          .splitExp 0 8
            (.missing 0 13)
            (.reject))
          (.step (.primeLo 2 281) <|
          .step (.dropHi 3 2867) <|
          .step (.primeHi 3 2861) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 3 2628) <|
            .step (.primeLo 3 2633) <|
            .splitBase 3 2741
              (.splitBase 2 281
                (.reject)
                (.step (.primeLo 2 283) <|
                .step (.dropHi 3 2673) <|
                .step (.primeHi 3 2671) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 3 2663) <|
                  .splitBase 3 2665
                    (.step (.primeHi 3 2663) <|
                    .reject)
                    (.step (.primeLo 3 2671) <|
                    .splitExp 1 4
                      (.reject)
                      (.splitExp 0 12
                        (.reject)
                        (.reject))))))
              (.step (.primeLo 3 2749) <|
              .step (.dropHi 2 282) <|
              .step (.primeHi 2 281) <|
              .step (.dropLo 3 2814) <|
              .step (.primeLo 3 2819) <|
              .splitExp 0 10
                (.missing 0 23)
                (.step (.dropLo 3 2855) <|
                .step (.primeLo 3 2857) <|
                .splitExp 1 4
                  (.splitExp 0 12
                    (.reject)
                    (.step (.dropLo 3 2859) <|
                    .step (.primeLo 3 2861) <|
                    .splitSpecial 9
                      (.missing 4 11)
                      (.splitExp 0 14
                        (.missing 0 11)
                        (.splitExp 2 2
                          (.missing 2 109)
                          (.reject)))))
                  (.step (.dropLo 3 2860) <|
                  .step (.primeLo 3 2861) <|
                  .splitExp 0 12
                    (.splitSpecial 9
                      (.missing 4 11)
                      (.reject))
                    (.reject)))))))))

theorem deficientFourPowerGeneralPart104 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,17,17,2,0⟩, ⟨false,277,293,2,0⟩, ⟨false,2190,3229,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart104Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
