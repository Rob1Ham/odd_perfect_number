module

public import OddPerfect.DeficientPowerReplayGeneral.Part014

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart070Tree : Tree :=
  .step (.dropLo 4 16) <|
  .step (.xLo 17) <|
  .splitBase 3 81
    (.step (.primeHi 3 79) <|
    .step (.dropLo 4 20) <|
    .step (.xLo 21) <|
    .splitBase 2 49
      (.use 0)
      (.step (.primeLo 2 53) <|
      .step (.primeLo 3 59) <|
      .step (.dropHi 4 35) <|
      .step (.xHi 33) <|
      .splitExp 1 2
        (.missing 1 31)
        (.step (.dropLo 4 24) <|
        .step (.xLo 25) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 31) <|
          .step (.xLo 33) <|
          .reject)
          (.step (.dropLo 4 26) <|
          .step (.xLo 29) <|
          .splitBase 2 61
            (.splitBase 3 67
              (.step (.dropLo 4 30) <|
              .step (.xLo 33) <|
              .missing 4 17)
              (.step (.primeLo 3 71) <|
              .step (.dropHi 4 32) <|
              .step (.xHi 29) <|
              .step (.dropLo 2 57) <|
              .step (.dropLo 3 73) <|
              .step (.primeLo 2 59) <|
              .splitBase 3 75
                (.step (.primeHi 3 73) <|
                .reject)
                (.step (.primeLo 3 79) <|
                .step (.dropHi 2 60) <|
                .step (.primeHi 2 59) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.reject))))
            (.step (.primeLo 2 67) <|
            .step (.primeLo 3 71) <|
            .reject)))))
    (.step (.primeLo 3 83) <|
    .step (.dropHi 4 40) <|
    .step (.xHi 37) <|
    .splitBase 2 49
      (.use 1)
      (.step (.primeLo 2 53) <|
      .step (.dropHi 4 30) <|
      .step (.xHi 29) <|
      .splitBase 3 165
        (.step (.primeHi 3 163) <|
        .step (.dropLo 4 18) <|
        .step (.xLo 21) <|
        .splitExp 1 2
          (.missing 1 31)
          (.splitBase 3 109
            (.step (.dropLo 4 22) <|
            .step (.xLo 25) <|
            .splitExp 0 4
              (.missing 0 11)
              (.splitBase 2 61
                (.splitBase 3 93
                  (.step (.primeHi 3 89) <|
                  .step (.dropLo 4 27) <|
                  .step (.xLo 29) <|
                  .step (.dropHi 2 58) <|
                  .step (.primeHi 2 53) <|
                  .reject)
                  (.step (.primeLo 3 97) <|
                  .step (.dropHi 4 28) <|
                  .step (.xHi 25) <|
                  .missing 4 13))
                (.step (.primeLo 2 67) <|
                .step (.dropHi 4 27) <|
                .step (.xHi 25) <|
                .missing 4 13)))
            (.step (.primeLo 3 113) <|
            .step (.dropHi 4 27) <|
            .step (.xHi 25) <|
            .splitExp 0 4
              (.missing 0 11)
              (.step (.dropLo 2 55) <|
              .step (.dropLo 4 22) <|
              .step (.primeLo 2 59) <|
              .step (.xLo 25) <|
              .missing 4 13))))
        (.step (.primeLo 3 167) <|
        .step (.dropHi 4 25) <|
        .splitExp 1 2
          (.missing 1 31)
          (.step (.dropLo 4 18) <|
          .step (.xLo 21) <|
          .splitBase 3 333
            (.step (.primeHi 3 331) <|
            .splitExp 0 4
              (.missing 0 11)
              (.splitBase 2 61
                (.step (.dropLo 4 22) <|
                .step (.xLo 25) <|
                .missing 4 13)
                (.step (.primeLo 2 67) <|
                .step (.dropHi 4 23) <|
                .step (.xHi 21) <|
                .missing 4 11)))
            (.step (.primeLo 3 337) <|
            .step (.dropHi 4 24) <|
            .step (.xHi 21) <|
            .missing 4 11)))))

private def deficientFourPowerGeneralPart070Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,37,49,2,0⟩, ⟨false,41,79,2,0⟩, ⟨true,21,77,5,0⟩], 1, deficientFourPowerGeneralPart067⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,37,49,2,0⟩, ⟨false,83,0,2,0⟩, ⟨true,17,37,5,0⟩], 1, deficientFourPowerGeneralPart069⟩]

theorem deficientFourPowerGeneralPart070 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,37,73,2,0⟩, ⟨false,41,0,2,0⟩, ⟨true,13,77,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart070Tree deficientFourPowerGeneralPart070Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart071Tree : Tree :=
  .step (.primeHi 3 40763) <|
  .splitExp 1 6
    (.step (.dropHi 3 35639) <|
    .step (.primeHi 3 35617) <|
    .splitExp 0 10
      (.missing 0 23)
      (.step (.dropLo 3 34738) <|
      .step (.primeLo 3 34739) <|
      .splitExp 0 12
        (.step (.dropHi 3 34860) <|
        .step (.primeHi 3 34849) <|
        .splitBase 3 34793
          (.step (.primeHi 3 34781) <|
          .splitExp 2 2
            (.missing 2 61)
            (.reject))
          (.step (.primeLo 3 34807) <|
          .splitExp 2 2
            (.missing 2 61)
            (.step (.dropLo 3 34810) <|
            .step (.primeLo 3 34819) <|
            .splitSpecial 5
              (.missing 4 7)
              (.reject))))
        (.step (.dropLo 3 35425) <|
        .step (.primeLo 3 35437) <|
        .splitBase 3 35525
          (.step (.primeHi 3 35521) <|
          .splitExp 0 14
            (.missing 0 11)
            (.step (.dropLo 3 35502) <|
            .step (.primeLo 3 35507) <|
            .splitExp 2 2
              (.missing 2 61)
              (.reject)))
          (.step (.primeLo 3 35527) <|
          .splitExp 0 14
            (.missing 0 11)
            (.splitExp 2 2
              (.missing 2 61)
              (.step (.dropLo 3 35577) <|
              .step (.primeLo 3 35591) <|
              .splitSpecial 5
                (.missing 4 7)
                (.reject)))))))
    (.reject)

theorem deficientFourPowerGeneralPart071 : Closed (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,29587,40765,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart071Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart072Tree : Tree :=
  .step (.primeLo 3 62981) <|
  .splitExp 0 12
    (.reject)
    (.splitExp 1 8
      (.missing 1 19)
      (.step (.dropLo 3 64727) <|
      .step (.primeLo 3 64747) <|
      .splitBase 3 65131
        (.step (.primeHi 3 65129) <|
        .splitExp 0 14
          (.missing 0 11)
          (.step (.dropLo 3 64988) <|
          .step (.primeLo 3 64997) <|
          .splitExp 2 2
            (.missing 2 61)
            (.reject)))
        (.step (.primeLo 3 65141) <|
        .splitExp 0 14
          (.missing 0 11)
          (.splitBase 3 65329
            (.step (.primeHi 3 65327) <|
            .splitExp 2 2
              (.missing 2 61)
              (.step (.dropLo 3 65238) <|
              .step (.primeLo 3 65239) <|
              .splitSpecial 5
                (.missing 4 7)
                (.reject)))
            (.step (.primeLo 3 65353) <|
            .splitExp 2 2
              (.missing 2 61)
              (.splitSpecial 5
                (.missing 4 7)
                (.step (.dropLo 3 65415) <|
                .step (.primeLo 3 65419) <|
                .splitExp 1 10
                  (.step (.dropHi 3 65448) <|
                  .step (.primeHi 3 65447) <|
                  .splitExp 0 16
                    (.missing 0 1871)
                    (.step (.dropLo 3 65444) <|
                    .step (.primeLo 3 65447) <|
                    .splitExp 0 18
                      (.missing 0 1597)
                      (.reject)))
                  (.step (.dropLo 3 65499) <|
                  .step (.primeLo 3 65519) <|
                  .splitExp 0 16
                    (.missing 0 1871)
                    (.reject)))))))))

theorem deficientFourPowerGeneralPart072 : Closed (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62974,65521,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart072Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart073Tree : Tree :=
  .step (.primeHi 2 257) <|
  .splitBase 3 2613
    (.step (.primeHi 3 2609) <|
    .step (.dropLo 2 232) <|
    .step (.primeLo 2 233) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 2 256) <|
      .step (.dropLo 3 2589) <|
      .step (.primeLo 2 257) <|
      .step (.primeLo 3 2591) <|
      .splitExp 1 4
        (.missing 1 11)
        (.reject)))
    (.step (.primeLo 3 2617) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 2 233) <|
      .splitExp 1 4
        (.missing 1 11)
        (.step (.dropLo 2 251) <|
        .step (.dropLo 3 12664) <|
        .step (.primeLo 3 12671) <|
        .splitBase 2 253
          (.step (.primeHi 2 251) <|
          .reject)
          (.step (.primeLo 2 257) <|
          .step (.dropHi 3 65536) <|
          .step (.primeHi 3 65521) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 3 29582) <|
            .step (.primeLo 3 29587) <|
            .splitBase 3 40765
              (.use 0)
              (.step (.primeLo 3 40771) <|
              .splitExp 1 6
                (.reject)
                (.step (.dropLo 3 46476) <|
                .step (.primeLo 3 46477) <|
                .splitExp 0 10
                  (.missing 0 23)
                  (.step (.dropLo 3 60612) <|
                  .step (.primeLo 3 60617) <|
                  .splitBase 3 62973
                    (.step (.primeHi 3 62971) <|
                    .splitExp 0 12
                      (.step (.dropHi 3 62948) <|
                      .step (.primeHi 3 62939) <|
                      .splitExp 1 8
                        (.missing 1 19)
                        (.step (.dropLo 3 62473) <|
                        .splitBase 3 62705
                          (.step (.primeHi 3 62701) <|
                          .splitExp 2 2
                            (.missing 2 61)
                            (.reject))
                          (.step (.primeLo 3 62723) <|
                          .splitExp 2 2
                            (.missing 2 61)
                            (.splitSpecial 5
                              (.missing 4 7)
                              (.step (.dropLo 3 62867) <|
                              .step (.primeLo 3 62869) <|
                              .splitExp 1 10
                                (.reject)
                                (.reject))))))
                      (.step (.dropLo 3 62732) <|
                      .step (.primeLo 3 62743) <|
                      .splitExp 1 8
                        (.missing 1 19)
                        (.reject)))
                    (.use 1)))))))))

private def deficientFourPowerGeneralPart073Refs : List Known := [
  ⟨#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,29587,40765,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart071⟩,
  ⟨#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,257,257,2,0⟩, ⟨false,62974,65521,2,0⟩, ⟨true,17,17,5,0⟩], 1, deficientFourPowerGeneralPart072⟩]

theorem deficientFourPowerGeneralPart073 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,223,261,2,0⟩, ⟨false,1307,0,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart073Tree deficientFourPowerGeneralPart073Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart074Tree : Tree :=
  .step (.primeHi 3 1583) <|
  .step (.dropLo 2 299) <|
  .step (.primeLo 2 307) <|
  .step (.dropHi 3 1536) <|
  .step (.primeHi 3 1531) <|
  .splitBase 3 1409
    (.splitBase 2 311
      (.step (.dropLo 3 1321) <|
      .splitExp 0 8
        (.missing 0 13)
        (.step (.dropLo 2 310) <|
        .step (.dropLo 3 1405) <|
        .step (.primeLo 2 311) <|
        .step (.primeLo 3 1409) <|
        .splitExp 1 6
          (.splitExp 0 10
            (.missing 0 23)
            (.reject))
          (.reject)))
      (.step (.primeLo 2 313) <|
      .step (.dropHi 3 1401) <|
      .step (.primeHi 3 1399) <|
      .splitExp 0 8
        (.missing 0 13)
        (.splitBase 3 1351
          (.step (.primeHi 3 1327) <|
          .step (.dropLo 2 315) <|
          .step (.primeLo 2 317) <|
          .step (.dropHi 3 1326) <|
          .step (.primeHi 3 1321) <|
          .splitExp 1 6
            (.reject)
            (.step (.dropLo 3 1315) <|
            .step (.primeLo 3 1319) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject)))
          (.step (.primeLo 3 1361) <|
          .step (.dropHi 2 315) <|
          .step (.primeHi 2 313) <|
          .step (.dropLo 3 1365) <|
          .step (.primeLo 3 1367) <|
          .splitExp 1 6
            (.step (.dropHi 3 1376) <|
            .step (.primeHi 3 1373) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject))
            (.step (.dropLo 3 1389) <|
            .step (.primeLo 3 1399) <|
            .splitExp 0 10
              (.missing 0 23)
              (.splitExp 0 12
                (.splitExp 1 8
                  (.missing 1 19)
                  (.reject))
                (.reject)))))))
    (.step (.primeLo 3 1423) <|
    .step (.dropHi 2 311) <|
    .splitExp 0 8
      (.missing 0 13)
      (.splitBase 3 1475
        (.step (.primeHi 3 1471) <|
        .splitBase 2 307
          (.reject)
          (.step (.primeLo 2 311) <|
          .step (.dropHi 3 1442) <|
          .step (.primeHi 3 1439) <|
          .splitExp 1 6
            (.reject)
            (.step (.dropLo 3 1430) <|
            .step (.primeLo 3 1433) <|
            .splitExp 0 10
              (.missing 0 23)
              (.reject))))
        (.step (.primeLo 3 1481) <|
        .step (.dropHi 2 309) <|
        .step (.primeHi 2 307) <|
        .step (.dropLo 3 1493) <|
        .splitExp 1 6
          (.step (.dropHi 3 1506) <|
          .step (.primeHi 3 1499) <|
          .splitExp 0 10
            (.missing 0 23)
            (.reject))
          (.step (.dropLo 3 1521) <|
          .step (.primeLo 3 1523) <|
          .splitExp 0 10
            (.missing 0 23)
            (.reject)))))

theorem deficientFourPowerGeneralPart074 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,293,317,2,0⟩, ⟨false,1307,1585,2,0⟩, ⟨true,17,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart074Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
