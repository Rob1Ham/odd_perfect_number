module

public import OddPerfect.DeficientPowerReplayGeneral.Part023

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart115Tree : Tree :=
  .step (.primeLo 2 367) <|
  .step (.dropHi 3 844) <|
  .step (.primeHi 3 839) <|
  .splitExp 0 6
    (.missing 0 1093)
    (.splitBase 3 707
      (.step (.primeHi 3 701) <|
      .splitBase 2 397
        (.splitExp 1 2
          (.missing 1 307)
          (.step (.dropLo 2 384) <|
          .step (.dropLo 3 663) <|
          .step (.primeLo 2 389) <|
          .step (.primeLo 3 673) <|
          .splitSpecial 5
            (.missing 4 7)
            (.step (.dropLo 2 394) <|
            .step (.dropLo 3 693) <|
            .step (.primeLo 2 397) <|
            .step (.primeLo 3 701) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject))))
        (.step (.primeLo 2 401) <|
        .splitExp 1 2
          (.missing 1 307)
          (.splitBase 3 653
            (.splitBase 2 415
              (.step (.primeHi 2 409) <|
              .step (.dropLo 3 632) <|
              .step (.primeLo 3 641) <|
              .splitSpecial 5
                (.missing 4 7)
                (.reject))
              (.step (.primeLo 2 419) <|
              .splitBase 3 631
                (.splitSpecial 5
                  (.missing 4 7)
                  (.step (.dropLo 2 420) <|
                  .step (.primeLo 2 421) <|
                  .splitExp 0 8
                    (.missing 0 13)
                    (.step (.dropLo 2 428) <|
                    .step (.dropLo 3 622) <|
                    .step (.primeLo 2 431) <|
                    .step (.primeLo 3 631) <|
                    .reject)))
                (.step (.primeLo 3 641) <|
                .step (.dropHi 2 425) <|
                .step (.primeHi 2 421) <|
                .splitSpecial 5
                  (.missing 4 7)
                  (.splitExp 0 8
                    (.missing 0 13)
                    (.step (.dropLo 3 648) <|
                    .step (.primeLo 3 653) <|
                    .step (.dropHi 2 420) <|
                    .step (.primeHi 2 419) <|
                    .reject)))))
            (.step (.primeLo 3 659) <|
            .step (.dropHi 2 417) <|
            .step (.primeHi 2 409) <|
            .splitBase 3 679
              (.step (.primeHi 3 677) <|
              .splitSpecial 5
                (.missing 4 7)
                (.step (.dropLo 2 402) <|
                .step (.primeLo 2 409) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.reject)))
              (.step (.primeLo 3 683) <|
              .step (.dropHi 2 408) <|
              .step (.primeHi 2 401) <|
              .splitSpecial 5
                (.missing 4 7)
                (.splitExp 0 8
                  (.missing 0 13)
                  (.reject)))))))
      (.use 0))

private def deficientFourPowerGeneralPart115Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,17,17,2,0⟩, ⟨false,367,433,2,0⟩, ⟨false,708,839,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart114⟩]

theorem deficientFourPowerGeneralPart115 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,360,433,2,0⟩, ⟨false,613,863,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart115Tree deficientFourPowerGeneralPart115Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart116Tree : Tree :=
  .step (.primeHi 3 977) <|
  .step (.dropLo 2 333) <|
  .step (.primeLo 2 337) <|
  .splitBase 2 347
    (.splitBase 3 923
      (.step (.primeHi 3 919) <|
      .step (.dropLo 2 340) <|
      .step (.primeLo 2 347) <|
      .splitSpecial 5
        (.missing 4 7)
        (.reject))
      (.step (.primeLo 3 929) <|
      .splitBase 2 341
        (.step (.primeHi 2 337) <|
        .step (.dropLo 3 945) <|
        .step (.primeLo 3 947) <|
        .splitSpecial 5
          (.missing 4 7)
          (.reject))
        (.step (.primeLo 2 347) <|
        .step (.dropHi 3 973) <|
        .step (.primeHi 3 971) <|
        .splitSpecial 5
          (.missing 4 7)
          (.splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 3 967) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject))))))
    (.step (.primeLo 2 349) <|
    .step (.dropHi 3 957) <|
    .step (.primeHi 3 953) <|
    .splitBase 3 913
      (.step (.primeHi 3 911) <|
      .splitSpecial 5
        (.missing 4 7)
        (.splitBase 2 353
          (.step (.dropLo 3 886) <|
          .step (.primeLo 3 887) <|
          .splitExp 0 8
            (.missing 0 13)
            (.reject))
          (.step (.primeLo 2 359) <|
          .step (.dropHi 3 889) <|
          .step (.primeHi 3 887) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 3 884) <|
            .step (.primeLo 3 887) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject)))))
      (.step (.primeLo 3 919) <|
      .step (.dropHi 2 354) <|
      .step (.primeHi 2 353) <|
      .splitSpecial 5
        (.missing 4 7)
        (.splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 3 923) <|
          .step (.primeLo 3 929) <|
          .step (.dropHi 2 352) <|
          .step (.primeHi 2 349) <|
          .step (.dropLo 3 952) <|
          .step (.primeLo 3 953) <|
          .splitExp 0 10
            (.missing 0 23)
            (.reject)))))

theorem deficientFourPowerGeneralPart116 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,359,2,0⟩, ⟨false,877,979,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart116Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart117Tree : Tree :=
  .step (.primeHi 3 1109) <|
  .splitBase 2 329
    (.step (.primeHi 2 317) <|
    .step (.dropLo 3 932) <|
    .step (.primeLo 3 937) <|
    .splitExp 1 2
      (.step (.fix 1 307 2) <|
      .step (.dropLo 3 1031) <|
      .splitSpecial 5
        (.missing 4 7)
        (.step (.dropLo 3 1104) <|
        .step (.primeLo 3 1109) <|
        .splitExp 0 8
          (.missing 0 13)
          (.reject)))
      (.reject))
    (.step (.primeLo 2 331) <|
    .splitExp 1 2
      (.missing 1 307)
      (.splitBase 3 979
        (.use 0)
        (.step (.primeLo 3 983) <|
        .step (.dropHi 2 345) <|
        .step (.primeHi 2 337) <|
        .splitBase 3 1041
          (.step (.primeHi 3 1039) <|
          .splitSpecial 5
            (.missing 4 7)
            (.step (.dropLo 2 333) <|
            .step (.dropLo 3 1006) <|
            .step (.primeLo 2 337) <|
            .step (.primeLo 3 1009) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject)))
          (.step (.primeLo 3 1049) <|
          .splitSpecial 5
            (.missing 4 7)
            (.splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 1054) <|
              .step (.primeLo 3 1061) <|
              .splitBase 2 333
                (.step (.primeHi 2 331) <|
                .reject)
                (.step (.primeLo 2 337) <|
                .step (.dropHi 3 1061) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.splitExp 1 4
                    (.splitExp 0 12
                      (.reject)
                      (.splitSpecial 9
                        (.missing 4 11)
                        (.reject)))
                    (.reject)))))))))

private def deficientFourPowerGeneralPart117Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,359,2,0⟩, ⟨false,877,979,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart116⟩]

theorem deficientFourPowerGeneralPart117 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,17,17,2,0⟩, ⟨false,307,359,2,0⟩, ⟨false,877,1115,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart117Tree deficientFourPowerGeneralPart117Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart118Tree : Tree :=
  .step (.primeLo 3 1297) <|
  .step (.dropHi 2 318) <|
  .step (.primeHi 2 317) <|
  .splitBase 3 1403
    (.step (.primeHi 3 1399) <|
    .splitBase 2 311
      (.splitSpecial 5
        (.missing 4 7)
        (.step (.dropLo 2 308) <|
        .step (.dropLo 3 1342) <|
        .step (.primeLo 2 311) <|
        .step (.primeLo 3 1361) <|
        .splitExp 0 8
          (.missing 0 13)
          (.reject)))
      (.step (.primeLo 2 313) <|
      .splitSpecial 5
        (.missing 4 7)
        (.splitExp 0 8
          (.missing 0 13)
          (.step (.dropLo 3 1314) <|
          .step (.primeLo 3 1319) <|
          .splitBase 3 1357
            (.step (.primeHi 3 1327) <|
            .step (.dropLo 2 316) <|
            .step (.primeLo 2 317) <|
            .step (.dropHi 3 1326) <|
            .step (.primeHi 3 1321) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject))
            (.step (.primeLo 3 1361) <|
            .step (.dropHi 2 315) <|
            .step (.primeHi 2 313) <|
            .step (.dropLo 3 1388) <|
            .step (.primeLo 3 1399) <|
            .splitExp 0 10
              (.missing 0 23)
              (.splitExp 1 4
                (.splitExp 0 12
                  (.reject)
                  (.reject))
                (.reject)))))))
    (.step (.primeLo 3 1409) <|
    .step (.dropHi 2 312) <|
    .step (.primeHi 2 311) <|
    .splitSpecial 5
      (.missing 4 7)
      (.splitExp 0 8
        (.missing 0 13)
        (.step (.dropLo 3 1429) <|
        .splitBase 3 1477
          (.step (.primeHi 3 1471) <|
          .step (.dropLo 2 309) <|
          .step (.primeLo 2 311) <|
          .step (.dropHi 3 1442) <|
          .step (.primeHi 3 1439) <|
          .splitExp 0 10
            (.missing 0 23)
            (.reject))
          (.step (.primeLo 3 1481) <|
          .step (.dropHi 2 309) <|
          .step (.primeHi 2 307) <|
          .step (.dropLo 3 1520) <|
          .step (.primeLo 3 1523) <|
          .splitExp 0 10
            (.missing 0 23)
            (.reject)))))

theorem deficientFourPowerGeneralPart118 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,331,2,0⟩, ⟨false,1292,1531,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart118Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart119Tree : Tree :=
  .step (.primeLo 3 613) <|
  .step (.dropHi 2 438) <|
  .step (.primeHi 2 433) <|
  .splitBase 3 875
    (.step (.primeHi 3 863) <|
    .splitBase 2 359
      (.splitExp 0 6
        (.missing 0 1093)
        (.step (.dropLo 2 325) <|
        .step (.dropLo 3 693) <|
        .step (.primeLo 2 331) <|
        .step (.primeLo 3 701) <|
        .splitExp 1 2
          (.missing 1 307)
          (.step (.dropLo 2 348) <|
          .step (.dropLo 3 806) <|
          .step (.primeLo 2 349) <|
          .step (.primeLo 3 809) <|
          .splitSpecial 5
            (.missing 4 7)
            (.step (.dropLo 2 356) <|
            .step (.dropLo 3 850) <|
            .step (.primeLo 2 359) <|
            .step (.primeLo 3 853) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject)))))
      (.use 0))
    (.step (.primeLo 3 877) <|
    .step (.dropHi 2 361) <|
    .step (.primeHi 2 359) <|
    .splitExp 0 6
      (.step (.fix 0 1093 3) <|
      .reject)
      (.splitBase 3 1115
        (.use 1)
        (.step (.primeLo 3 1117) <|
        .step (.dropHi 2 331) <|
        .splitExp 1 2
          (.step (.fix 1 307 2) <|
          .step (.dropHi 3 1170) <|
          .step (.primeHi 3 1163) <|
          .splitSpecial 5
            (.missing 4 7)
            (.splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 1162) <|
              .step (.primeLo 3 1163) <|
              .splitExp 0 10
                (.missing 0 23)
                (.reject))))
          (.splitBase 3 1291
            (.splitBase 2 317
              (.step (.dropLo 3 1150) <|
              .step (.primeLo 3 1151) <|
              .splitBase 2 311
                (.step (.dropLo 3 1236) <|
                .step (.primeLo 3 1237) <|
                .splitSpecial 5
                  (.missing 4 7)
                  (.reject))
                (.step (.primeLo 2 313) <|
                .splitBase 3 1215
                  (.step (.primeHi 3 1213) <|
                  .splitSpecial 5
                    (.missing 4 7)
                    (.reject))
                  (.step (.primeLo 3 1217) <|
                  .splitSpecial 5
                    (.missing 4 7)
                    (.step (.dropLo 3 1241) <|
                    .step (.primeLo 3 1249) <|
                    .splitExp 0 8
                      (.missing 0 13)
                      (.reject)))))
              (.step (.primeLo 2 331) <|
              .step (.dropHi 3 1126) <|
              .step (.primeHi 3 1123) <|
              .splitSpecial 5
                (.missing 4 7)
                (.splitExp 0 8
                  (.missing 0 13)
                  (.step (.dropLo 3 1118) <|
                  .step (.primeLo 3 1123) <|
                  .splitExp 0 10
                    (.missing 0 23)
                    (.reject)))))
            (.use 2)))))

private def deficientFourPowerGeneralPart119Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,360,433,2,0⟩, ⟨false,613,863,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart115⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,17,17,2,0⟩, ⟨false,307,359,2,0⟩, ⟨false,877,1115,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart117⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,331,2,0⟩, ⟨false,1292,1531,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart118⟩]

theorem deficientFourPowerGeneralPart119 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,307,503,2,0⟩, ⟨false,608,1531,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart119Tree deficientFourPowerGeneralPart119Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
