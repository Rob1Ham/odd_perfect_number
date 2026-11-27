module

public import OddPerfect.DeficientTree

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def closedSecond17Tree : Tree :=
  .step (.primeLo 2 19) <|
  .step (.primeLo 3 23) <|
  .step (.dropHi 2 3520) <|
  .step (.dropHi 4 7) <|
  .step (.primeHi 2 3517) <|
  .step (.xHi 5) <|
  .splitBase 2 37
    (.splitExp 0 2
      (.missing 0 13)
      (.step (.dropLo 2 20) <|
      .step (.dropLo 3 46) <|
      .step (.primeLo 2 23) <|
      .step (.primeLo 3 47) <|
      .step (.dropHi 3 3520) <|
      .step (.primeHi 3 3517) <|
      .splitBase 3 91
        (.step (.primeHi 3 89) <|
        .step (.dropLo 2 26) <|
        .step (.primeLo 2 29) <|
        .splitBase 3 61
          (.step (.dropLo 2 31) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 2 35) <|
            .step (.dropLo 3 56) <|
            .step (.primeLo 2 37) <|
            .step (.primeLo 3 59) <|
            .reject))
          (.step (.primeLo 3 67) <|
          .step (.dropHi 2 34) <|
          .step (.primeHi 2 31) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 3 79) <|
            .splitBase 2 29
              (.reject)
              (.step (.primeLo 2 31) <|
              .step (.dropHi 3 84) <|
              .step (.primeHi 3 83) <|
              .splitBase 3 79
                (.reject)
                (.step (.primeLo 3 83) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.splitExp 1 2
                    (.missing 1 307)
                    (.reject)))))))
        (.step (.primeLo 3 97) <|
        .step (.dropHi 2 29) <|
        .splitBase 3 187
          (.step (.primeHi 3 181) <|
          .splitBase 2 25
            (.step (.primeHi 2 23) <|
            .reject)
            (.step (.primeLo 2 29) <|
            .step (.dropHi 3 104) <|
            .step (.primeHi 3 103) <|
            .splitExp 0 4
              (.missing 0 11)
              (.splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 3 101) <|
                .splitExp 1 2
                  (.missing 1 307)
                  (.reject)))))
          (.step (.primeLo 3 191) <|
          .step (.dropHi 2 25) <|
          .step (.primeHi 2 23) <|
          .step (.dropLo 3 213) <|
          .step (.primeLo 3 223) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 3 973) <|
            .step (.primeLo 3 977) <|
            .splitBase 3 1529
              (.step (.primeHi 3 1523) <|
              .splitExp 0 6
                (.step (.fix 0 1093 3) <|
                .splitExp 1 2
                  (.missing 1 307)
                  (.reject))
                (.reject))
              (.step (.primeLo 3 1531) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 3 1611) <|
                .step (.primeLo 3 1613) <|
                .splitBase 3 2211
                  (.step (.primeHi 3 2207) <|
                  .splitExp 1 2
                    (.missing 1 307)
                    (.reject))
                  (.step (.primeLo 3 2213) <|
                  .splitExp 1 2
                    (.missing 1 307)
                    (.step (.dropLo 3 2393) <|
                    .splitBase 3 2847
                      (.step (.primeHi 3 2843) <|
                      .splitExp 2 2
                        (.missing 2 7)
                        (.reject))
                      (.step (.primeLo 3 2851) <|
                      .splitExp 2 2
                        (.missing 2 7)
                        (.step (.dropLo 3 2978) <|
                        .step (.primeLo 3 2999) <|
                        .splitExp 0 8
                          (.missing 0 13)
                          (.step (.dropLo 3 3441) <|
                          .step (.primeLo 3 3449) <|
                          .splitExp 0 10
                            (.step (.dropHi 3 3451) <|
                            .step (.primeHi 3 3449) <|
                            .splitExp 1 4
                              (.reject)
                              (.reject))
                            (.step (.dropLo 3 3501) <|
                            .step (.primeLo 3 3511) <|
                            .splitExp 1 4
                              (.step (.dropHi 3 3511) <|
                              .splitExp 0 12
                                (.reject)
                                (.splitExp 2 4
                                  (.reject)
                                  (.splitExp 0 14
                                    (.missing 0 11)
                                    (.reject))))
                              (.splitExp 0 12
                                (.step (.dropHi 3 3512) <|
                                .step (.primeHi 3 3511) <|
                                .splitExp 2 4
                                  (.reject)
                                  (.reject))
                                (.reject)))))))))))))))
    (.step (.primeLo 2 41) <|
    .step (.primeLo 3 43) <|
    .step (.dropHi 2 47) <|
    .step (.dropHi 3 50) <|
    .step (.primeHi 3 47) <|
    .step (.primeHi 2 43) <|
    .splitExp 0 2
      (.missing 0 13)
      (.splitExp 0 4
        (.missing 0 11)
        (.step (.dropLo 2 42) <|
        .step (.dropLo 3 46) <|
        .step (.primeLo 2 43) <|
        .step (.primeLo 3 47) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.reject))))

theorem closedSecond17 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,17,17,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,5,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound closedSecond17Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
