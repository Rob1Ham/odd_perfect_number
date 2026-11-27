module

public import OddPerfect.DeficientPowerReplayGeneral.Part005

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart025Tree : Tree :=
  .step (.dropLo 4 45087) <|
  .step (.xLo 45089) <|
  .splitExp 0 10
    (.step (.grow 0 23) <|
    .step (.dropHi 4 47838) <|
    .step (.xLo 45149) <|
    .step (.xHi 47817) <|
    .splitExp 2 4
      (.step (.dropHi 4 46279) <|
      .step (.xHi 46253) <|
      .splitExp 1 8
        (.step (.grow 1 19) <|
        .missing 1 31)
        (.step (.dropLo 4 46109) <|
        .step (.xLo 46161) <|
        .splitExp 3 2
          (.missing 3 61)
          (.step (.dropLo 4 46235) <|
          .step (.xLo 46253) <|
          .missing 4 13)))
      (.step (.dropLo 4 46561) <|
      .step (.xLo 46621) <|
      .splitExp 1 8
        (.step (.grow 1 19) <|
        .missing 1 31)
        (.step (.dropLo 4 47651) <|
        .step (.xLo 47725) <|
        .splitExp 3 2
          (.missing 3 61)
          (.step (.dropLo 4 47785) <|
          .step (.xLo 47817) <|
          .splitExp 1 10
            (.reject)
            (.reject)))))
    (.step (.dropLo 4 58271) <|
    .step (.xLo 58273) <|
    .splitExp 2 4
      (.step (.dropHi 4 62644) <|
      .step (.xHi 62641) <|
      .splitExp 0 12
        (.step (.dropHi 4 60276) <|
        .step (.xHi 60273) <|
        .splitExp 1 8
          (.step (.grow 1 19) <|
          .step (.grow 1 31) <|
          .missing 1 829)
          (.step (.dropLo 4 59989) <|
          .splitExp 3 2
            (.step (.grow 3 61) <|
            .missing 3 1087)
            (.step (.dropLo 4 60201) <|
            .splitExp 1 10
              (.step (.dropHi 4 60201) <|
              .reject)
              (.reject))))
        (.step (.dropLo 4 60227) <|
        .step (.xLo 60229) <|
        .splitExp 1 8
          (.step (.grow 1 19) <|
          .step (.grow 1 31) <|
          .missing 1 829)
          (.step (.dropLo 4 62064) <|
          .step (.xLo 62065) <|
          .splitExp 0 14
            (.step (.grow 0 11) <|
            .step (.grow 0 13) <|
            .step (.dropHi 4 62372) <|
            .step (.xLo 62205) <|
            .step (.xHi 62205) <|
            .missing 4 19)
            (.step (.dropLo 4 62304) <|
            .step (.xLo 62305) <|
            .splitExp 3 2
              (.step (.grow 3 61) <|
              .missing 3 1087)
              (.step (.dropLo 4 62534) <|
              .step (.xLo 62537) <|
              .splitExp 1 10
                (.step (.dropHi 4 62564) <|
                .step (.xHi 62561) <|
                .splitExp 0 16
                  (.missing 0 1871)
                  (.step (.dropLo 4 62560) <|
                  .step (.xLo 62561) <|
                  .splitExp 0 18
                    (.missing 0 1597)
                    (.reject)))
                (.step (.dropLo 4 62610) <|
                .step (.xLo 62613) <|
                .splitExp 0 16
                  (.missing 0 1871)
                  (.step (.dropLo 4 62637) <|
                  .splitExp 0 18
                    (.missing 0 1597)
                    (.step (.dropLo 4 62640) <|
                    .step (.xLo 62641) <|
                    .splitExp 1 12
                      (.splitExp 0 20
                        (.missing 0 13)
                        (.reject))
                      (.reject)))))))))
      (.use 0))

private def deficientFourPowerGeneralPart025Refs : List Known := [
  ⟨#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,58273,65533,5,0⟩], 1, deficientFourPowerGeneralPart024⟩]

theorem deficientFourPowerGeneralPart025 : Closed (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,29013,65533,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart025Tree deficientFourPowerGeneralPart025Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart026Tree : Tree :=
  .step (.primeHi 3 257) <|
  .step (.dropLo 4 12558) <|
  .step (.xLo 12561) <|
  .splitExp 0 8
    (.step (.grow 0 13) <|
    .step (.grow 0 757) <|
    .step (.dropHi 4 15137) <|
    .step (.xLo 49205) <|
    .reject)
    (.step (.dropLo 4 29013) <|
    .splitExp 1 6
      (.step (.dropHi 4 35639) <|
      .step (.xHi 35637) <|
      .splitExp 0 10
        (.step (.grow 0 23) <|
        .step (.dropHi 4 29670) <|
        .step (.xLo 29049) <|
        .step (.xHi 29601) <|
        .splitExp 2 4
          (.step (.dropHi 4 29063) <|
          .step (.xHi 29049) <|
          .missing 4 7)
          (.reject))
        (.step (.dropLo 4 33957) <|
        .splitExp 2 4
          (.step (.dropHi 4 34767) <|
          .step (.xHi 34765) <|
          .splitExp 0 12
            (.step (.dropHi 4 34025) <|
            .splitExp 3 2
              (.step (.grow 3 61) <|
              .missing 3 1087)
              (.reject))
            (.step (.dropLo 4 34612) <|
            .step (.xLo 34613) <|
            .splitExp 0 14
              (.step (.grow 0 11) <|
              .step (.grow 0 13) <|
              .step (.dropHi 4 34683) <|
              .step (.xLo 34749) <|
              .reject)
              (.step (.dropLo 4 34686) <|
              .step (.xLo 34689) <|
              .splitExp 3 2
                (.step (.grow 3 61) <|
                .missing 3 1087)
                (.step (.dropLo 4 34757) <|
                .splitExp 0 16
                  (.missing 0 1871)
                  (.reject)))))
          (.step (.dropLo 4 34786) <|
          .step (.xLo 34789) <|
          .splitExp 0 12
            (.step (.dropHi 4 34860) <|
            .step (.xHi 34857) <|
            .splitExp 3 2
              (.missing 3 61)
              (.reject))
            (.step (.dropLo 4 35474) <|
            .step (.xLo 35477) <|
            .splitExp 0 14
              (.step (.grow 0 11) <|
              .missing 0 13)
              (.step (.dropLo 4 35552) <|
              .step (.xLo 35553) <|
              .splitExp 3 2
                (.missing 3 61)
                (.step (.dropLo 4 35626) <|
                .step (.xLo 35629) <|
                .splitExp 0 16
                  (.missing 0 1871)
                  (.step (.dropLo 4 35635) <|
                  .step (.xLo 35637) <|
                  .missing 4 103)))))))
      (.use 0))

private def deficientFourPowerGeneralPart026Refs : List Known := [
  ⟨#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,29013,65533,5,0⟩], 1, deficientFourPowerGeneralPart025⟩]

theorem deficientFourPowerGeneralPart026 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,259,2,0⟩, ⟨true,5929,65533,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart026Tree deficientFourPowerGeneralPart026Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart027Tree : Tree :=
  .step (.dropLo 4 8986) <|
  .step (.xLo 8989) <|
  .splitExp 0 10
    (.step (.grow 0 23) <|
    .step (.dropHi 4 9090) <|
    .step (.xLo 8993) <|
    .step (.xHi 9085) <|
    .splitExp 2 4
      (.step (.dropHi 4 9032) <|
      .step (.xHi 8993) <|
      .missing 4 1499)
      (.step (.dropLo 4 9043) <|
      .step (.xLo 9085) <|
      .missing 4 7))
    (.step (.dropLo 4 9410) <|
    .step (.xLo 9413) <|
    .splitExp 2 4
      (.step (.dropHi 4 9517) <|
      .splitExp 0 12
        (.step (.dropHi 4 9461) <|
        .splitExp 1 8
          (.missing 1 19)
          (.step (.dropLo 4 9454) <|
          .step (.xLo 9457) <|
          .splitExp 3 2
            (.step (.grow 3 7) <|
            .missing 3 13)
            (.step (.dropLo 4 9459) <|
            .step (.xLo 9461) <|
            .missing 4 19)))
        (.step (.dropLo 4 9460) <|
        .step (.xLo 9461) <|
        .splitExp 1 8
          (.step (.grow 1 19) <|
          .missing 1 31)
          (.step (.dropLo 4 9504) <|
          .step (.xLo 9505) <|
          .splitExp 0 14
            (.missing 0 11)
            (.step (.dropLo 4 9509) <|
            .splitExp 3 2
              (.step (.grow 3 7) <|
              .missing 3 13)
              (.step (.dropLo 4 9514) <|
              .step (.xLo 9517) <|
              .splitExp 1 10
                (.reject)
                (.splitExp 0 16
                  (.missing 0 1871)
                  (.reject)))))))
      (.step (.dropLo 4 9473) <|
      .splitExp 0 12
        (.step (.dropHi 4 9524) <|
        .step (.xHi 9521) <|
        .splitExp 1 8
          (.step (.grow 1 19) <|
          .missing 1 31)
          (.step (.dropLo 4 9517) <|
          .splitExp 3 2
            (.missing 3 7)
            (.reject)))
        (.step (.dropLo 4 9523) <|
        .step (.xLo 9525) <|
        .splitExp 1 8
          (.step (.grow 1 19) <|
          .missing 1 31)
          (.step (.dropLo 4 9568) <|
          .step (.xLo 9569) <|
          .splitExp 0 14
            (.step (.grow 0 11) <|
            .step (.grow 0 13) <|
            .step (.dropHi 4 9575) <|
            .step (.xLo 9581) <|
            .reject)
            (.step (.dropLo 4 9573) <|
            .splitExp 3 2
              (.missing 3 7)
              (.step (.dropLo 4 9578) <|
              .step (.xLo 9581) <|
              .missing 4 1597))))))

theorem deficientFourPowerGeneralPart027 : Closed (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,8093,9581,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart027Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart028Tree : Tree :=
  .step (.primeHi 3 263) <|
  .step (.dropLo 4 1473) <|
  .splitExp 1 4
    (.step (.grow 1 11) <|
    .step (.grow 1 71) <|
    .step (.dropHi 4 4133) <|
    .step (.xLo 3905) <|
    .step (.xHi 3905) <|
    .missing 4 7)
    (.step (.dropLo 4 2691) <|
    .step (.xLo 2693) <|
    .splitExp 2 2
      (.step (.grow 2 307) <|
      .step (.dropHi 4 7972) <|
      .step (.xLo 3377) <|
      .step (.xHi 7061) <|
      .step (.dropHi 3 262) <|
      .step (.primeHi 3 257) <|
      .step (.dropLo 4 3540) <|
      .step (.xLo 4605) <|
      .step (.dropHi 3 256) <|
      .step (.primeHi 3 251) <|
      .step (.dropLo 4 5288) <|
      .step (.xLo 5833) <|
      .splitExp 0 8
        (.missing 0 13)
        (.step (.dropLo 4 6947) <|
        .step (.xLo 7061) <|
        .missing 4 11))
      (.step (.dropLo 4 5926) <|
      .step (.xLo 5929) <|
      .splitBase 3 255
        (.step (.primeHi 3 251) <|
        .reject)
        (.step (.primeLo 3 257) <|
        .step (.dropHi 4 65536) <|
        .step (.xHi 65533) <|
        .splitBase 3 259
          (.use 0)
          (.step (.primeLo 3 263) <|
          .step (.dropHi 4 9581) <|
          .splitExp 0 8
            (.step (.grow 0 13) <|
            .missing 0 757)
            (.step (.dropLo 4 8092) <|
            .step (.xLo 8093) <|
            .splitExp 1 6
              (.step (.dropHi 4 8535) <|
              .step (.xHi 8533) <|
              .splitExp 0 10
                (.step (.grow 0 23) <|
                .step (.dropHi 4 8142) <|
                .step (.xLo 8165) <|
                .reject)
                (.step (.dropLo 4 8435) <|
                .step (.xLo 8437) <|
                .splitExp 2 4
                  (.step (.dropHi 4 8484) <|
                  .step (.xHi 8481) <|
                  .splitExp 0 12
                    (.step (.dropHi 4 8439) <|
                    .step (.xHi 8437) <|
                    .splitExp 3 2
                      (.missing 3 7)
                      (.reject))
                    (.step (.dropLo 4 8475) <|
                    .step (.xLo 8477) <|
                    .splitExp 0 14
                      (.step (.grow 0 11) <|
                      .missing 0 13)
                      (.step (.dropLo 4 8479) <|
                      .step (.xLo 8481) <|
                      .splitExp 3 2
                        (.missing 3 7)
                        (.reject))))
                  (.step (.dropLo 4 8485) <|
                  .splitExp 0 12
                    (.step (.dropHi 4 8489) <|
                    .splitExp 3 2
                      (.missing 3 7)
                      (.reject))
                    (.step (.dropLo 4 8525) <|
                    .splitExp 0 14
                      (.step (.grow 0 11) <|
                      .missing 0 13)
                      (.step (.dropLo 4 8530) <|
                      .step (.xLo 8533) <|
                      .missing 4 251)))))
              (.use 1))))))

private def deficientFourPowerGeneralPart028Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,259,2,0⟩, ⟨true,5929,65533,5,0⟩], 1, deficientFourPowerGeneralPart026⟩,
  ⟨#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,8093,9581,5,0⟩], 1, deficientFourPowerGeneralPart027⟩]

theorem deficientFourPowerGeneralPart028 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,251,265,2,0⟩, ⟨true,1085,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart028Tree deficientFourPowerGeneralPart028Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart029Tree : Tree :=
  .step (.primeLo 3 271) <|
  .step (.dropHi 4 4608) <|
  .step (.xHi 4605) <|
  .splitExp 1 6
    (.step (.dropHi 4 4351) <|
    .step (.xHi 4349) <|
    .splitExp 0 10
      (.step (.grow 0 23) <|
      .step (.dropHi 4 4247) <|
      .step (.xLo 4301) <|
      .reject)
      (.step (.dropLo 4 4325) <|
      .splitExp 2 4
        (.step (.dropHi 4 4338) <|
        .step (.xHi 4337) <|
        .splitExp 0 12
          (.step (.dropHi 4 4326) <|
          .step (.xHi 4325) <|
          .missing 4 7)
          (.step (.dropLo 4 4335) <|
          .step (.xLo 4337) <|
          .missing 4 241))
        (.step (.dropLo 4 4338) <|
        .step (.xLo 4341) <|
        .splitExp 0 12
          (.reject)
          (.reject))))
    (.step (.dropLo 4 4465) <|
    .splitExp 0 10
      (.step (.grow 0 23) <|
      .step (.dropHi 4 4491) <|
      .step (.xLo 4485) <|
      .step (.xHi 4485) <|
      .splitExp 2 4
        (.reject)
        (.splitExp 1 8
          (.missing 1 19)
          (.reject)))
      (.step (.dropLo 4 4568) <|
      .step (.xLo 4569) <|
      .splitExp 2 4
        (.step (.dropHi 4 4593) <|
        .splitExp 0 12
          (.step (.dropHi 4 4579) <|
          .step (.xHi 4577) <|
          .splitExp 1 8
            (.missing 1 19)
            (.reject))
          (.step (.dropLo 4 4579) <|
          .step (.xLo 4581) <|
          .splitExp 1 8
            (.missing 1 19)
            (.step (.dropLo 4 4590) <|
            .step (.xLo 4593) <|
            .splitExp 0 14
              (.missing 0 11)
              (.splitExp 3 2
                (.reject)
                (.splitExp 1 10
                  (.reject)
                  (.splitExp 0 16
                    (.missing 0 1871)
                    (.reject)))))))
        (.step (.dropLo 4 4582) <|
        .step (.xLo 4585) <|
        .splitExp 0 12
          (.step (.dropHi 4 4594) <|
          .step (.xHi 4593) <|
          .splitExp 1 8
            (.missing 1 19)
            (.reject))
          (.step (.dropLo 4 4594) <|
          .step (.xLo 4597) <|
          .splitExp 1 8
            (.missing 1 19)
            (.step (.dropLo 4 4604) <|
            .step (.xLo 4605) <|
            .missing 4 7)))))

theorem deficientFourPowerGeneralPart029 : Closed (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,270,271,2,0⟩, ⟨true,4233,5277,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart029Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
