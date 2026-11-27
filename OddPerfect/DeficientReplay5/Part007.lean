module

public import OddPerfect.DeficientReplay5.Part006

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour5Part030Tree : Tree :=
  .step (.primeLo 3 577) <|
  .step (.dropHi 4 458) <|
  .step (.xHi 457) <|
  .splitExp 0 6
    (.missing 0 1093)
    (.step (.dropLo 4 301) <|
    .splitBase 3 689
      (.use 0)
      (.step (.primeLo 3 691) <|
      .step (.dropHi 4 405) <|
      .splitExp 1 4
        (.step (.grow 1 11) <|
        .missing 1 71)
        (.step (.dropLo 4 332) <|
        .step (.xLo 333) <|
        .splitBase 3 765
          (.step (.primeHi 3 761) <|
          .step (.dropLo 4 349) <|
          .splitExp 2 2
            (.missing 2 307)
            (.step (.dropLo 4 375) <|
            .step (.xLo 377) <|
            .splitBase 3 723
              (.step (.primeHi 3 719) <|
              .step (.dropLo 4 387) <|
              .step (.xLo 389) <|
              .splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 4 394) <|
                .step (.xLo 397) <|
                .step (.dropHi 3 715) <|
                .step (.primeHi 3 709) <|
                .splitBase 3 699
                  (.step (.primeHi 3 691) <|
                  .step (.dropLo 4 402) <|
                  .step (.xLo 405) <|
                  .missing 4 7)
                  (.step (.primeLo 3 701) <|
                  .step (.dropHi 4 401) <|
                  .splitExp 1 6
                    (.step (.dropHi 4 399) <|
                    .step (.xHi 397) <|
                    .missing 4 199)
                    (.step (.dropLo 4 399) <|
                    .step (.xLo 401) <|
                    .missing 4 67))))
              (.step (.primeLo 3 727) <|
              .step (.dropHi 4 393) <|
              .splitExp 0 8
                (.step (.grow 0 13) <|
                .step (.fix 0 757 3) <|
                .step (.dropHi 4 377) <|
                .missing 4 7)
                (.step (.dropLo 4 382) <|
                .step (.xLo 385) <|
                .step (.dropHi 3 758) <|
                .step (.primeHi 3 757) <|
                .splitBase 3 741
                  (.step (.primeHi 3 739) <|
                  .step (.dropLo 4 388) <|
                  .step (.xLo 389) <|
                  .splitBase 3 731
                    (.step (.primeHi 3 727) <|
                    .step (.dropLo 4 391) <|
                    .step (.xLo 393) <|
                    .missing 4 197)
                    (.step (.primeLo 3 733) <|
                    .step (.dropHi 4 391) <|
                    .step (.xHi 389) <|
                    .missing 4 13))
                  (.step (.primeLo 3 743) <|
                  .step (.dropHi 4 389) <|
                  .splitBase 3 749
                    (.step (.primeHi 3 743) <|
                    .step (.dropLo 4 387) <|
                    .step (.xLo 389) <|
                    .missing 4 13)
                    (.step (.primeLo 3 751) <|
                    .step (.dropHi 4 386) <|
                    .step (.xHi 385) <|
                    .missing 4 193))))))
          (.step (.primeLo 3 769) <|
          .step (.dropHi 4 382) <|
          .step (.xHi 381) <|
          .splitExp 2 2
            (.missing 2 307)
            (.step (.dropLo 4 355) <|
            .step (.xLo 357) <|
            .splitBase 3 811
              (.step (.dropLo 4 364) <|
              .step (.xLo 365) <|
              .splitExp 0 8
                (.step (.grow 0 13) <|
                .missing 0 757)
                (.step (.dropLo 4 370) <|
                .step (.xLo 373) <|
                .step (.dropHi 3 809) <|
                .splitBase 3 787
                  (.step (.dropLo 4 376) <|
                  .step (.xLo 377) <|
                  .splitBase 3 777
                    (.step (.primeHi 3 773) <|
                    .step (.dropLo 4 379) <|
                    .step (.xLo 381) <|
                    .missing 4 191)
                    (.step (.primeLo 3 787) <|
                    .step (.dropHi 4 377) <|
                    .missing 4 7))
                  (.step (.primeLo 3 797) <|
                  .step (.dropHi 4 375) <|
                  .step (.xHi 373) <|
                  .missing 4 11)))
              (.step (.primeLo 3 821) <|
              .step (.dropHi 4 370) <|
              .step (.xHi 369) <|
              .splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 4 361) <|
                .splitBase 3 839
                  (.step (.dropLo 4 365) <|
                  .splitBase 3 829
                    (.step (.dropLo 4 367) <|
                    .step (.xLo 369) <|
                    .missing 4 37)
                    (.step (.primeLo 3 839) <|
                    .step (.dropHi 4 366) <|
                    .step (.xHi 365) <|
                    .missing 4 61))
                  (.step (.primeLo 3 853) <|
                  .step (.dropHi 4 364) <|
                  .step (.xHi 361) <|
                  .missing 4 181))))))))

private def deficientFour5Part030Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,577,689,2,0⟩, ⟨true,301,457,1,1⟩], 1, deficientFour5Part029⟩]

theorem deficientFour5Part030 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,574,859,2,0⟩, ⟨true,269,625,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part030Tree deficientFour5Part030Refs _ _ (by decide +kernel)

private def deficientFour5Part031Tree : Tree :=
  .step (.primeLo 3 1543) <|
  .step (.dropHi 4 305) <|
  .splitBase 3 1627
    (.splitExp 0 8
      (.missing 0 13)
      (.step (.dropLo 4 301) <|
      .splitBase 3 1583
        (.step (.dropLo 4 303) <|
        .step (.xLo 305) <|
        .step (.dropHi 3 1561) <|
        .step (.primeHi 3 1559) <|
        .splitExp 1 6
          (.reject)
          (.step (.dropLo 3 1545) <|
          .step (.primeLo 3 1549) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 3 1557) <|
            .step (.primeLo 3 1559) <|
            .splitExp 2 4
              (.splitExp 0 12
                (.reject)
                (.splitExp 1 8
                  (.missing 1 19)
                  (.reject)))
              (.splitExp 0 12
                (.splitExp 1 8
                  (.missing 1 19)
                  (.reject))
                (.reject)))))
        (.step (.primeLo 3 1597) <|
        .step (.dropHi 4 303) <|
        .step (.xHi 301) <|
        .missing 4 151)))
    (.step (.primeLo 3 1637) <|
    .step (.dropHi 4 302) <|
    .step (.xHi 301) <|
    .splitExp 0 8
      (.missing 0 13)
      (.step (.dropLo 4 298) <|
      .step (.xLo 301) <|
      .missing 4 151))

theorem deficientFour5Part031 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,1534,1723,2,0⟩, ⟨true,297,313,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part031Tree [] _ _ (by decide +kernel)

private def deficientFour5Part032Tree : Tree :=
  .step (.primeLo 3 1151) <|
  .step (.dropHi 4 327) <|
  .step (.xHi 325) <|
  .splitExp 1 4
    (.step (.grow 1 11) <|
    .missing 1 71)
    (.step (.dropLo 4 278) <|
    .step (.xLo 281) <|
    .splitBase 3 1379
      (.step (.primeHi 3 1373) <|
      .step (.dropLo 4 290) <|
      .step (.xLo 293) <|
      .splitExp 2 2
        (.missing 2 307)
        (.step (.dropLo 4 308) <|
        .step (.xLo 309) <|
        .splitBase 3 1251
          (.step (.primeHi 3 1249) <|
          .step (.dropLo 4 315) <|
          .step (.xLo 317) <|
          .splitBase 3 1197
            (.step (.primeHi 3 1193) <|
            .step (.dropLo 4 319) <|
            .step (.xLo 321) <|
            .splitExp 0 8
              (.step (.grow 0 13) <|
              .missing 0 757)
              (.step (.dropLo 3 1162) <|
              .step (.dropLo 4 323) <|
              .step (.primeLo 3 1163) <|
              .step (.xLo 325) <|
              .missing 4 163))
            (.step (.primeLo 3 1201) <|
            .step (.dropHi 4 324) <|
            .step (.xHi 321) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 1216) <|
              .step (.dropLo 4 319) <|
              .step (.primeLo 3 1217) <|
              .step (.xLo 321) <|
              .missing 4 7)))
          (.step (.primeLo 3 1259) <|
          .step (.dropHi 4 320) <|
          .step (.xHi 317) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 3 1276) <|
            .step (.dropLo 4 312) <|
            .step (.primeLo 3 1277) <|
            .step (.xLo 313) <|
            .splitBase 3 1323
              (.step (.primeHi 3 1321) <|
              .step (.dropLo 4 315) <|
              .step (.xLo 317) <|
              .missing 4 53)
              (.step (.primeLo 3 1327) <|
              .step (.dropHi 4 315) <|
              .step (.xHi 313) <|
              .missing 4 157)))))
      (.step (.primeLo 3 1381) <|
      .step (.dropHi 4 313) <|
      .splitExp 2 2
        (.missing 2 307)
        (.step (.dropLo 4 294) <|
        .step (.xLo 297) <|
        .splitBase 3 1533
          (.step (.primeHi 3 1531) <|
          .step (.dropLo 4 301) <|
          .splitBase 3 1451
            (.step (.dropLo 4 304) <|
            .step (.xLo 305) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 4 308) <|
              .step (.xLo 309) <|
              .splitBase 3 1415
                (.step (.primeHi 3 1409) <|
                .step (.dropLo 4 310) <|
                .step (.xLo 313) <|
                .missing 4 157)
                (.step (.primeLo 3 1423) <|
                .step (.dropHi 4 310) <|
                .step (.xHi 309) <|
                .missing 4 31)))
            (.step (.primeLo 3 1453) <|
            .step (.dropHi 4 309) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 4 305) <|
              .splitBase 3 1489
                (.step (.dropLo 4 307) <|
                .step (.xLo 309) <|
                .missing 4 31)
                (.step (.primeLo 3 1493) <|
                .step (.dropHi 4 307) <|
                .step (.xHi 305) <|
                .step (.dropLo 3 1516) <|
                .step (.primeLo 3 1523) <|
                .splitExp 1 6
                  (.splitExp 0 10
                    (.missing 0 23)
                    (.step (.dropLo 3 1527) <|
                    .step (.primeLo 3 1531) <|
                    .splitExp 2 4
                      (.reject)
                      (.splitExp 0 12
                        (.reject)
                        (.splitExp 0 14
                          (.missing 0 11)
                          (.splitExp 0 16
                            (.missing 0 1871)
                            (.reject))))))
                  (.reject)))))
          (.use 0))))

private def deficientFour5Part032Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,1534,1723,2,0⟩, ⟨true,297,313,1,1⟩], 1, deficientFour5Part031⟩]

theorem deficientFour5Part032 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,1150,1723,2,0⟩, ⟨true,257,361,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part032Tree deficientFour5Part032Refs _ _ (by decide +kernel)

private def deficientFour5Part033Tree : Tree :=
  .step (.dropLo 4 256) <|
  .step (.xLo 257) <|
  .splitBase 3 1149
    (.step (.primeHi 3 1129) <|
    .step (.dropLo 4 278) <|
    .step (.xLo 281) <|
    .splitExp 1 4
      (.step (.grow 1 11) <|
      .missing 1 71)
      (.step (.dropLo 4 303) <|
      .step (.xLo 305) <|
      .splitBase 3 977
        (.step (.dropLo 4 317) <|
        .splitExp 2 2
          (.missing 2 307)
          (.step (.dropLo 4 339) <|
          .step (.xLo 341) <|
          .splitBase 3 915
            (.step (.primeHi 3 911) <|
            .step (.dropLo 4 347) <|
            .step (.xLo 349) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 4 353) <|
              .splitBase 3 885
                (.step (.primeHi 3 883) <|
                .step (.dropLo 4 357) <|
                .splitBase 3 871
                  (.step (.primeHi 3 863) <|
                  .step (.dropLo 4 361) <|
                  .missing 4 181)
                  (.step (.primeLo 3 877) <|
                  .step (.dropHi 4 360) <|
                  .step (.xHi 357) <|
                  .missing 4 179))
                (.step (.primeLo 3 887) <|
                .step (.dropHi 4 358) <|
                .step (.xHi 357) <|
                .splitBase 3 897
                  (.step (.primeHi 3 887) <|
                  .step (.dropLo 4 357) <|
                  .missing 4 179)
                  (.step (.primeLo 3 907) <|
                  .step (.dropHi 4 355) <|
                  .step (.xHi 353) <|
                  .missing 4 59))))
            (.step (.primeLo 3 919) <|
            .step (.dropHi 4 353) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 4 344) <|
              .step (.xLo 345) <|
              .splitBase 3 947
                (.step (.dropLo 4 348) <|
                .step (.xLo 349) <|
                .splitBase 3 931
                  (.step (.primeHi 3 929) <|
                  .step (.dropLo 4 350) <|
                  .step (.xLo 353) <|
                  .missing 4 59)
                  (.step (.primeLo 3 937) <|
                  .step (.dropHi 4 350) <|
                  .step (.xHi 349) <|
                  .missing 4 7))
                (.step (.primeLo 3 953) <|
                .step (.dropHi 4 348) <|
                .step (.xHi 345) <|
                .missing 4 173)))))
        (.step (.primeLo 3 983) <|
        .step (.dropHi 4 344) <|
        .step (.xHi 341) <|
        .splitExp 2 2
          (.missing 2 307)
          (.step (.dropLo 4 323) <|
          .step (.xLo 325) <|
          .splitBase 3 1049
            (.step (.dropLo 4 331) <|
            .step (.xLo 333) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 995) <|
              .step (.dropLo 4 336) <|
              .step (.primeLo 3 997) <|
              .step (.xLo 337) <|
              .splitBase 3 1021
                (.step (.dropLo 4 339) <|
                .step (.xLo 341) <|
                .missing 4 19)
                (.step (.primeLo 3 1031) <|
                .step (.dropHi 4 339) <|
                .step (.xHi 337) <|
                .missing 4 13)))
            (.step (.primeLo 3 1051) <|
            .step (.dropHi 4 337) <|
            .splitExp 0 8
              (.step (.grow 0 13) <|
              .missing 0 757)
              (.step (.dropLo 4 328) <|
              .step (.xLo 329) <|
              .splitBase 3 1087
                (.step (.dropLo 4 332) <|
                .step (.xLo 333) <|
                .splitBase 3 1067
                  (.step (.primeHi 3 1063) <|
                  .step (.dropLo 4 334) <|
                  .step (.xLo 337) <|
                  .missing 4 13)
                  (.step (.primeLo 3 1069) <|
                  .step (.dropHi 4 335) <|
                  .step (.xHi 333) <|
                  .missing 4 167))
                (.step (.primeLo 3 1091) <|
                .step (.dropHi 4 333) <|
                .splitBase 3 1109
                  (.step (.dropLo 4 330) <|
                  .step (.xLo 333) <|
                  .missing 4 167)
                  (.step (.primeLo 3 1117) <|
                  .step (.dropHi 4 330) <|
                  .step (.xHi 329) <|
                  .missing 4 11))))))))
    (.use 0)

private def deficientFour5Part033Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,1150,1723,2,0⟩, ⟨true,257,361,1,1⟩], 1, deficientFour5Part032⟩]

theorem deficientFour5Part033 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,863,1723,2,0⟩, ⟨true,233,361,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part033Tree deficientFour5Part033Refs _ _ (by decide +kernel)

private def deficientFour5Part034Tree : Tree :=
  .step (.primeHi 3 3463) <|
  .step (.dropLo 4 238) <|
  .step (.xLo 241) <|
  .splitExp 1 4
    (.step (.grow 1 11) <|
    .missing 1 71)
    (.step (.dropLo 4 257) <|
    .splitBase 3 2309
      (.step (.dropLo 4 267) <|
      .step (.xLo 269) <|
      .splitExp 2 2
        (.missing 2 307)
        (.step (.dropLo 4 282) <|
        .step (.xLo 285) <|
        .splitBase 3 1979
          (.step (.dropLo 4 288) <|
          .step (.xLo 289) <|
          .splitBase 3 1847
            (.step (.dropLo 4 291) <|
            .step (.xLo 293) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 1749) <|
              .step (.dropLo 4 295) <|
              .step (.primeLo 3 1753) <|
              .step (.xLo 297) <|
              .missing 4 149))
            (.step (.primeLo 3 1861) <|
            .step (.dropHi 4 295) <|
            .step (.xHi 293) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 1902) <|
              .step (.dropLo 4 292) <|
              .step (.primeLo 3 1907) <|
              .step (.xLo 293) <|
              .missing 4 7)))
          (.step (.primeLo 3 1987) <|
          .step (.dropHi 4 292) <|
          .step (.xHi 289) <|
          .splitBase 3 2135
            (.step (.primeHi 3 2131) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 2088) <|
              .step (.dropLo 4 289) <|
              .step (.primeLo 3 2089) <|
              .missing 4 29))
            (.step (.primeLo 3 2137) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 4 286) <|
              .step (.xLo 289) <|
              .missing 4 29)))))
      (.step (.primeLo 3 2311) <|
      .step (.dropHi 4 286) <|
      .step (.xHi 285) <|
      .splitExp 2 2
        (.missing 2 307)
        (.step (.dropLo 4 271) <|
        .step (.xLo 273) <|
        .splitBase 3 2771
          (.step (.primeHi 3 2767) <|
          .step (.dropLo 4 276) <|
          .step (.xLo 277) <|
          .splitBase 3 2517
            (.step (.primeHi 3 2503) <|
            .step (.dropLo 4 279) <|
            .step (.xLo 281) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 2323) <|
              .step (.dropLo 4 283) <|
              .step (.primeLo 3 2333) <|
              .step (.xLo 285) <|
              .missing 4 11))
            (.step (.primeLo 3 2521) <|
            .step (.dropHi 4 283) <|
            .step (.xHi 281) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 2627) <|
              .step (.dropLo 4 280) <|
              .step (.primeLo 3 2633) <|
              .step (.xLo 281) <|
              .missing 4 47)))
          (.step (.primeLo 3 2777) <|
          .step (.dropHi 4 280) <|
          .step (.xHi 277) <|
          .splitBase 3 3081
            (.step (.primeHi 3 3079) <|
            .step (.dropLo 4 274) <|
            .step (.xLo 277) <|
            .missing 4 139)
            (.step (.primeLo 3 3083) <|
            .splitExp 0 8
              (.step (.grow 0 13) <|
              .missing 0 757)
              (.step (.dropLo 4 274) <|
              .step (.xLo 277) <|
              .missing 4 139))))))

theorem deficientFour5Part034 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,1733,3465,2,0⟩, ⟨true,225,297,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part034Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
