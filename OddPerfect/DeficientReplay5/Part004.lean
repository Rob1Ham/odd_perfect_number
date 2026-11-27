module

public import OddPerfect.DeficientReplay5.Part003

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour5Part015Tree : Tree :=
  .step (.dropLo 4 45087) <|
  .step (.xLo 45089) <|
  .splitExp 0 10
    (.step (.grow 0 23) <|
    .step (.dropHi 4 47837) <|
    .step (.xLo 45149) <|
    .step (.xHi 47817) <|
    .splitExp 2 4
      (.step (.dropHi 4 46278) <|
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
      (.step (.dropHi 4 62643) <|
      .step (.xHi 62641) <|
      .splitExp 0 12
        (.step (.dropHi 4 60275) <|
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
              (.reject)
              (.step (.dropLo 4 60273) <|
              .splitExp 1 12
                (.reject)
                (.reject)))))
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
            .step (.dropHi 4 62371) <|
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
                (.step (.dropHi 4 62563) <|
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
                      (.reject)
                      (.reject)))))))))
      (.use 0))

private def deficientFour5Part015Refs : List Known := [
  ⟨#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,58273,65533,1,1⟩], 1, deficientFour5Part014⟩]

theorem deficientFour5Part015 : Closed (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,29013,65533,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part015Tree deficientFour5Part015Refs _ _ (by decide +kernel)

private def deficientFour5Part016Tree : Tree :=
  .step (.primeHi 3 257) <|
  .step (.dropLo 4 12558) <|
  .step (.xLo 12561) <|
  .splitExp 0 8
    (.step (.grow 0 13) <|
    .step (.grow 0 757) <|
    .step (.dropHi 4 15136) <|
    .step (.xLo 49205) <|
    .reject)
    (.step (.dropLo 4 29013) <|
    .splitExp 1 6
      (.step (.dropHi 4 35638) <|
      .step (.xHi 35637) <|
      .splitExp 0 10
        (.step (.grow 0 23) <|
        .step (.dropHi 4 29669) <|
        .step (.xLo 29049) <|
        .step (.xHi 29601) <|
        .splitExp 2 4
          (.step (.dropHi 4 29062) <|
          .step (.xHi 29049) <|
          .missing 4 7)
          (.reject))
        (.step (.dropLo 4 33957) <|
        .splitExp 2 4
          (.step (.dropHi 4 34766) <|
          .step (.xHi 34765) <|
          .splitExp 0 12
            (.step (.dropHi 4 34024) <|
            .step (.xHi 34021) <|
            .splitExp 3 2
              (.step (.grow 3 61) <|
              .missing 3 1087)
              (.reject))
            (.step (.dropLo 4 34612) <|
            .step (.xLo 34613) <|
            .splitExp 0 14
              (.step (.grow 0 11) <|
              .step (.grow 0 13) <|
              .step (.dropHi 4 34682) <|
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
            (.step (.dropHi 4 34859) <|
            .step (.xHi 34857) <|
            .splitExp 3 2
              (.missing 3 61)
              (.step (.dropLo 4 34857) <|
              .missing 4 29))
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

private def deficientFour5Part016Refs : List Known := [
  ⟨#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,29013,65533,1,1⟩], 1, deficientFour5Part015⟩]

theorem deficientFour5Part016 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,259,2,0⟩, ⟨true,5929,65533,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part016Tree deficientFour5Part016Refs _ _ (by decide +kernel)

private def deficientFour5Part017Tree : Tree :=
  .step (.dropLo 4 8986) <|
  .step (.xLo 8989) <|
  .splitExp 0 10
    (.step (.grow 0 23) <|
    .step (.dropHi 4 9089) <|
    .step (.xLo 8993) <|
    .step (.xHi 9085) <|
    .splitExp 2 4
      (.step (.dropHi 4 9031) <|
      .step (.xHi 8993) <|
      .missing 4 1499)
      (.step (.dropLo 4 9043) <|
      .step (.xLo 9085) <|
      .missing 4 7))
    (.step (.dropLo 4 9410) <|
    .step (.xLo 9413) <|
    .splitExp 2 4
      (.step (.dropHi 4 9516) <|
      .step (.xHi 9513) <|
      .splitExp 0 12
        (.step (.dropHi 4 9460) <|
        .step (.xHi 9457) <|
        .splitExp 1 8
          (.missing 1 19)
          (.step (.dropLo 4 9454) <|
          .step (.xLo 9457) <|
          .splitExp 3 2
            (.step (.grow 3 7) <|
            .missing 3 13)
            (.reject)))
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
              (.reject)))))
      (.step (.dropLo 4 9473) <|
      .splitExp 0 12
        (.step (.dropHi 4 9523) <|
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
            (.missing 0 11)
            (.step (.dropLo 4 9573) <|
            .splitExp 3 2
              (.missing 3 7)
              (.reject))))))

theorem deficientFour5Part017 : Closed (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,8093,9577,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part017Tree [] _ _ (by decide +kernel)

private def deficientFour5Part018Tree : Tree :=
  .step (.primeLo 3 271) <|
  .step (.dropHi 4 4607) <|
  .step (.xHi 4605) <|
  .splitExp 1 6
    (.step (.dropHi 4 4350) <|
    .step (.xHi 4349) <|
    .splitExp 0 10
      (.step (.grow 0 23) <|
      .step (.dropHi 4 4246) <|
      .step (.xLo 4301) <|
      .reject)
      (.step (.dropLo 4 4325) <|
      .splitExp 2 4
        (.step (.dropHi 4 4337) <|
        .splitExp 0 12
          (.step (.dropHi 4 4325) <|
          .missing 4 7)
          (.step (.dropLo 4 4335) <|
          .step (.xLo 4337) <|
          .missing 4 241))
        (.step (.dropLo 4 4338) <|
        .step (.xLo 4341) <|
        .splitExp 0 12
          (.reject)
          (.step (.dropLo 4 4349) <|
          .missing 4 29))))
    (.step (.dropLo 4 4465) <|
    .splitExp 0 10
      (.step (.grow 0 23) <|
      .step (.dropHi 4 4490) <|
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
        (.step (.dropHi 4 4592) <|
        .step (.xHi 4589) <|
        .splitExp 0 12
          (.step (.dropHi 4 4578) <|
          .step (.xHi 4577) <|
          .splitExp 1 8
            (.missing 1 19)
            (.reject))
          (.step (.dropLo 4 4579) <|
          .step (.xLo 4581) <|
          .splitExp 1 8
            (.missing 1 19)
            (.reject)))
        (.step (.dropLo 4 4582) <|
        .step (.xLo 4585) <|
        .splitExp 0 12
          (.step (.dropHi 4 4593) <|
          .splitExp 1 8
            (.missing 1 19)
            (.step (.dropLo 4 4593) <|
            .splitExp 3 2
              (.reject)
              (.reject)))
          (.step (.dropLo 4 4594) <|
          .step (.xLo 4597) <|
          .splitExp 1 8
            (.missing 1 19)
            (.step (.dropLo 4 4604) <|
            .step (.xLo 4605) <|
            .missing 4 7)))))

theorem deficientFour5Part018 : Closed (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,270,271,2,0⟩, ⟨true,4233,5273,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part018Tree [] _ _ (by decide +kernel)

private def deficientFour5Part019Tree : Tree :=
  .step (.primeLo 3 277) <|
  .step (.dropHi 4 3363) <|
  .step (.xHi 3361) <|
  .splitExp 0 8
    (.step (.grow 0 13) <|
    .missing 0 757)
    (.step (.dropLo 4 2717) <|
    .splitBase 3 277
      (.step (.dropLo 4 3160) <|
      .step (.xLo 3161) <|
      .splitExp 1 6
        (.step (.dropHi 4 3224) <|
        .step (.xHi 3221) <|
        .splitExp 0 10
          (.step (.grow 0 23) <|
          .step (.dropHi 4 3167) <|
          .step (.xLo 3197) <|
          .reject)
          (.step (.dropLo 4 3211) <|
          .step (.xLo 3213) <|
          .splitExp 2 4
            (.step (.dropHi 4 3217) <|
            .splitExp 0 12
              (.reject)
              (.step (.dropLo 4 3217) <|
              .missing 4 1609))
            (.step (.dropLo 4 3218) <|
            .step (.xLo 3221) <|
            .missing 4 179)))
        (.step (.dropLo 4 3288) <|
        .step (.xLo 3289) <|
        .splitExp 0 10
          (.step (.grow 0 23) <|
          .step (.dropHi 4 3300) <|
          .step (.xHi 3289) <|
          .missing 4 7)
          (.step (.dropLo 4 3343) <|
          .step (.xLo 3345) <|
          .splitExp 2 4
            (.step (.dropHi 4 3355) <|
            .step (.xHi 3353) <|
            .splitExp 0 12
              (.step (.dropHi 4 3348) <|
              .step (.xHi 3345) <|
              .missing 4 7)
              (.step (.dropLo 4 3349) <|
              .splitExp 1 8
                (.missing 1 19)
                (.reject)))
            (.step (.dropLo 4 3351) <|
            .step (.xLo 3353) <|
            .splitExp 0 12
              (.step (.dropHi 4 3356) <|
              .step (.xHi 3353) <|
              .missing 4 13)
              (.step (.dropLo 4 3357) <|
              .splitExp 1 8
                (.missing 1 19)
                (.reject))))))
      (.step (.primeLo 3 281) <|
      .step (.dropHi 4 2866) <|
      .step (.xHi 2865) <|
      .splitExp 1 6
        (.step (.dropHi 4 2764) <|
        .step (.xHi 2761) <|
        .splitExp 0 10
          (.step (.grow 0 23) <|
          .step (.dropHi 4 2722) <|
          .step (.xLo 2737) <|
          .reject)
          (.step (.dropLo 4 2755) <|
          .step (.xLo 2757) <|
          .splitExp 2 4
            (.step (.dropHi 4 2759) <|
            .step (.xHi 2757) <|
            .missing 4 7)
            (.step (.dropLo 4 2760) <|
            .step (.xLo 2761) <|
            .missing 4 1381)))
        (.step (.dropLo 4 2811) <|
        .step (.xLo 2813) <|
        .splitExp 0 10
          (.step (.grow 0 23) <|
          .step (.dropHi 4 2820) <|
          .step (.xLo 2829) <|
          .reject)
          (.step (.dropLo 4 2851) <|
          .step (.xLo 2853) <|
          .splitExp 2 4
            (.step (.dropHi 4 2860) <|
            .step (.xHi 2857) <|
            .splitExp 0 12
              (.step (.dropHi 4 2855) <|
              .step (.xHi 2853) <|
              .missing 4 1427)
              (.step (.dropLo 4 2856) <|
              .step (.xLo 2857) <|
              .missing 4 1429))
            (.step (.dropLo 4 2857) <|
            .splitExp 0 12
              (.step (.dropHi 4 2861) <|
              .splitExp 1 8
                (.missing 1 19)
                (.step (.dropLo 4 2861) <|
                .missing 4 53))
              (.step (.dropLo 4 2862) <|
              .step (.xLo 2865) <|
              .missing 4 1433))))))

theorem deficientFour5Part019 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,274,281,2,0⟩, ⟨true,2421,5273,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part019Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
