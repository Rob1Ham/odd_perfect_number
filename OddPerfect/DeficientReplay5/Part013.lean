module

public import OddPerfect.DeficientReplay5.Part012

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour5Part060Tree : Tree :=
  .step (.primeHi 3 691) <|
  .step (.dropLo 2 149) <|
  .splitBase 2 167
    (.step (.dropLo 3 465) <|
    .step (.primeLo 3 467) <|
    .splitBase 2 157
      (.step (.dropLo 3 566) <|
      .step (.primeLo 3 569) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.reject))
      (.step (.primeLo 2 163) <|
      .splitBase 3 557
        (.splitExp 0 6
          (.missing 0 1093)
          (.reject))
        (.step (.primeLo 3 563) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 3 573) <|
          .step (.primeLo 3 577) <|
          .splitExp 1 4
            (.missing 1 11)
            (.reject)))))
    (.step (.primeLo 2 173) <|
    .step (.dropHi 3 632) <|
    .step (.primeHi 3 631) <|
    .splitBase 3 447
      (.step (.primeHi 3 443) <|
      .splitBase 3 389
        (.step (.dropLo 2 179) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.reject))
        (.step (.primeLo 3 397) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 2 182) <|
          .step (.primeLo 2 191) <|
          .splitExp 1 4
            (.missing 1 11)
            (.reject))))
      (.step (.primeLo 3 449) <|
      .splitBase 3 523
        (.use 0)
        (.step (.primeLo 3 541) <|
        .step (.dropHi 2 181) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.splitExp 1 4
            (.missing 1 11)
            (.splitBase 3 581
              (.step (.primeHi 3 577) <|
              .step (.dropLo 2 175) <|
              .step (.primeLo 2 179) <|
              .step (.dropHi 3 562) <|
              .step (.primeHi 3 557) <|
              .splitExp 0 8
                (.missing 0 13)
                (.splitBase 2 179
                  (.reject)
                  (.step (.primeLo 2 181) <|
                  .step (.dropHi 3 544) <|
                  .step (.primeHi 3 541) <|
                  .splitExp 1 6
                    (.reject)
                    (.reject))))
              (.step (.primeLo 3 587) <|
              .step (.dropHi 2 176) <|
              .step (.primeHi 2 173) <|
              .step (.dropLo 3 607) <|
              .splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 3 624) <|
                .step (.primeLo 3 631) <|
                .splitExp 1 6
                  (.reject)
                  (.splitExp 0 10
                    (.missing 0 23)
                    (.reject)))))))))

private def deficientFour5Part060Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,173,193,2,0⟩, ⟨false,449,523,2,0⟩, ⟨true,17,17,1,1⟩], 1, deficientFour5Part059⟩]

theorem deficientFour5Part060 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,127,193,2,0⟩, ⟨false,347,693,2,0⟩, ⟨true,17,17,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part060Tree deficientFour5Part060Refs _ _ (by decide +kernel)

private def deficientFour5Part061Tree : Tree :=
  .splitBase 2 137
    (.reject)
    (.step (.primeLo 2 139) <|
    .step (.dropHi 3 6256) <|
    .step (.primeHi 3 6247) <|
    .splitExp 0 8
      (.missing 0 13)
      (.step (.dropLo 3 5597) <|
      .step (.primeLo 3 5623) <|
      .splitBase 3 5917
        (.step (.primeHi 3 5903) <|
        .splitExp 1 6
          (.step (.dropHi 3 5792) <|
          .step (.primeHi 3 5791) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 3 5758) <|
            .step (.primeLo 3 5779) <|
            .splitExp 0 12
              (.reject)
              (.splitExp 2 2
                (.missing 2 13)
                (.step (.dropLo 3 5789) <|
                .step (.primeLo 3 5791) <|
                .splitExp 0 14
                  (.missing 0 11)
                  (.reject)))))
          (.reject))
        (.step (.primeLo 3 5923) <|
        .splitExp 1 6
          (.reject)
          (.step (.dropLo 3 6010) <|
          .step (.primeLo 3 6011) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 3 6197) <|
            .splitBase 3 6221
              (.splitExp 0 12
                (.splitExp 1 8
                  (.missing 1 19)
                  (.step (.dropLo 3 6216) <|
                  .step (.primeLo 3 6217) <|
                  .splitExp 2 2
                    (.missing 2 13)
                    (.reject)))
                (.step (.dropLo 3 6218) <|
                .step (.primeLo 3 6221) <|
                .splitExp 1 8
                  (.missing 1 19)
                  (.reject)))
              (.step (.primeLo 3 6229) <|
              .splitExp 0 12
                (.step (.dropHi 3 6231) <|
                .step (.primeHi 3 6229) <|
                .splitExp 1 8
                  (.missing 1 19)
                  (.splitExp 2 2
                    (.missing 2 13)
                    (.reject)))
                (.splitExp 1 8
                  (.missing 1 19)
                  (.step (.dropLo 3 6237) <|
                  .step (.primeLo 3 6247) <|
                  .splitExp 2 2
                    (.missing 2 13)
                    (.reject)))))))))

theorem deficientFour5Part061 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,137,139,2,0⟩, ⟨false,4481,7213,2,0⟩, ⟨true,17,17,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part061Tree [] _ _ (by decide +kernel)

private def deficientFour5Part062Tree : Tree :=
  .step (.primeLo 3 15761) <|
  .splitExp 1 6
    (.reject)
    (.step (.dropLo 3 16498) <|
    .step (.primeLo 3 16519) <|
    .splitExp 0 10
      (.missing 0 23)
      (.step (.dropLo 3 17987) <|
      .splitBase 3 18235
        (.step (.primeHi 3 18233) <|
        .splitExp 0 12
          (.splitBase 3 18109
            (.step (.primeHi 3 18097) <|
            .splitExp 1 8
              (.missing 1 19)
              (.reject))
            (.step (.primeLo 3 18119) <|
            .splitExp 1 8
              (.missing 1 19)
              (.step (.dropLo 3 18148) <|
              .step (.primeLo 3 18149) <|
              .splitExp 2 2
                (.missing 2 7)
                (.reject))))
          (.step (.dropLo 3 18169) <|
          .splitExp 1 8
            (.missing 1 19)
            (.reject)))
        (.step (.primeLo 3 18251) <|
        .splitExp 0 12
          (.step (.dropHi 3 18283) <|
          .step (.primeHi 3 18269) <|
          .splitExp 1 8
            (.missing 1 19)
            (.splitExp 2 2
              (.missing 2 7)
              (.reject)))
          (.splitBase 3 18371
            (.splitExp 1 8
              (.missing 1 19)
              (.step (.dropLo 3 18333) <|
              .step (.primeLo 3 18341) <|
              .splitExp 2 2
                (.missing 2 7)
                (.reject)))
            (.step (.primeLo 3 18379) <|
            .splitExp 1 8
              (.missing 1 19)
              (.splitExp 2 2
                (.missing 2 7)
                (.step (.dropLo 3 18465) <|
                .step (.primeLo 3 18481) <|
                .splitExp 0 14
                  (.missing 0 11)
                  (.step (.dropLo 3 18486) <|
                  .step (.primeLo 3 18493) <|
                  .splitExp 1 10
                    (.reject)
                    (.reject)))))))))

theorem deficientFour5Part062 : Closed (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,137,137,2,0⟩, ⟨false,15754,18493,2,0⟩, ⟨true,17,17,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part062Tree [] _ _ (by decide +kernel)

private def deficientFour5Part063Tree : Tree :=
  .step (.primeHi 2 139) <|
  .step (.dropLo 3 1067) <|
  .step (.primeLo 3 1069) <|
  .splitBase 3 2137
    (.step (.dropLo 2 130) <|
    .step (.primeLo 2 131) <|
    .splitExp 0 6
      (.step (.fix 0 1093 3) <|
      .step (.dropLo 2 138) <|
      .step (.primeLo 2 139) <|
      .splitExp 1 4
        (.missing 1 11)
        (.reject))
      (.step (.dropLo 2 137) <|
      .step (.dropLo 3 1883) <|
      .step (.primeLo 3 1889) <|
      .splitExp 1 4
        (.missing 1 11)
        (.reject)))
    (.step (.primeLo 3 2141) <|
    .splitBase 2 131
      (.splitExp 0 6
        (.missing 0 1093)
        (.step (.dropLo 2 129) <|
        .step (.dropLo 3 11295) <|
        .step (.primeLo 2 131) <|
        .step (.primeLo 3 11299) <|
        .splitExp 1 4
          (.missing 1 11)
          (.reject)))
      (.step (.primeLo 2 137) <|
      .step (.dropHi 3 18496) <|
      .step (.primeHi 3 18493) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.splitExp 1 4
          (.missing 1 11)
          (.step (.dropLo 3 4468) <|
          .step (.primeLo 3 4481) <|
          .splitBase 3 7213
            (.use 0)
            (.step (.primeLo 3 7219) <|
            .step (.dropHi 2 138) <|
            .step (.primeHi 2 137) <|
            .step (.dropLo 3 8470) <|
            .step (.primeLo 3 8501) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 13717) <|
              .step (.primeLo 3 13721) <|
              .splitBase 3 15753
                (.step (.primeHi 3 15749) <|
                .splitExp 1 6
                  (.step (.dropHi 3 14955) <|
                  .step (.primeHi 3 14951) <|
                  .splitExp 0 10
                    (.missing 0 23)
                    (.step (.dropLo 3 14731) <|
                    .splitBase 3 14839
                      (.step (.primeHi 3 14831) <|
                      .splitExp 0 12
                        (.step (.dropHi 3 14816) <|
                        .step (.primeHi 3 14813) <|
                        .splitExp 2 2
                          (.missing 2 7)
                          (.reject))
                        (.reject))
                      (.step (.primeLo 3 14843) <|
                      .splitExp 0 12
                        (.reject)
                        (.step (.dropLo 3 14853) <|
                        .step (.primeLo 3 14867) <|
                        .splitExp 2 2
                          (.missing 2 7)
                          (.step (.dropLo 3 14939) <|
                          .splitExp 0 14
                            (.missing 0 11)
                            (.reject))))))
                  (.reject))
                (.use 1)))))))

private def deficientFour5Part063Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,137,139,2,0⟩, ⟨false,4481,7213,2,0⟩, ⟨true,17,17,1,1⟩], 1, deficientFour5Part061⟩,
  ⟨#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,137,137,2,0⟩, ⟨false,15754,18493,2,0⟩, ⟨true,17,17,1,1⟩], 1, deficientFour5Part062⟩]

theorem deficientFour5Part063 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,127,143,2,0⟩, ⟨false,701,0,2,0⟩, ⟨true,17,17,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part063Tree deficientFour5Part063Refs _ _ (by decide +kernel)

private def deficientFour5Part064Tree : Tree :=
  .step (.primeLo 3 967) <|
  .step (.dropHi 2 158) <|
  .step (.primeHi 2 157) <|
  .splitExp 0 6
    (.step (.fix 0 1093 3) <|
    .reject)
    (.splitExp 1 4
      (.missing 1 11)
      (.splitBase 3 1187
        (.step (.dropLo 2 151) <|
        .splitBase 2 153
          (.step (.primeHi 2 151) <|
          .reject)
          (.step (.primeLo 2 157) <|
          .step (.dropHi 3 1010) <|
          .step (.primeHi 3 1009) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 3 991) <|
            .splitBase 3 999
              (.step (.primeHi 3 997) <|
              .splitExp 1 6
                (.splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 3 996) <|
                  .step (.primeLo 3 997) <|
                  .splitExp 0 12
                    (.reject)
                    (.reject)))
                (.reject))
              (.step (.primeLo 3 1009) <|
              .splitExp 1 6
                (.reject)
                (.splitExp 0 10
                  (.missing 0 23)
                  (.splitExp 0 12
                    (.splitExp 1 8
                      (.missing 1 19)
                      (.reject))
                    (.reject)))))))
        (.step (.primeLo 3 1193) <|
        .step (.dropHi 2 153) <|
        .step (.primeHi 2 151) <|
        .step (.dropLo 3 1251) <|
        .step (.primeLo 3 1259) <|
        .splitBase 3 1385
          (.step (.primeHi 3 1381) <|
          .splitBase 2 149
            (.reject)
            (.step (.primeLo 2 151) <|
            .step (.dropHi 3 1360) <|
            .step (.primeHi 3 1327) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 1326) <|
              .step (.primeLo 3 1327) <|
              .splitExp 1 6
                (.splitExp 0 10
                  (.missing 0 23)
                  (.reject))
                (.reject))))
          (.step (.primeLo 3 1399) <|
          .step (.dropHi 2 150) <|
          .step (.primeHi 2 149) <|
          .step (.dropLo 3 1408) <|
          .step (.primeLo 3 1409) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 3 1504) <|
            .step (.primeLo 3 1511) <|
            .splitExp 1 6
              (.step (.dropHi 3 1518) <|
              .step (.primeHi 3 1511) <|
              .splitExp 0 10
                (.missing 0 23)
                (.reject))
              (.step (.dropLo 3 1532) <|
              .step (.primeLo 3 1543) <|
              .splitExp 0 10
                (.missing 0 23)
                (.reject)))))))

theorem deficientFour5Part064 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,964,1543,2,0⟩, ⟨true,17,17,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part064Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
