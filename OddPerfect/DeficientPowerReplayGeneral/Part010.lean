module

public import OddPerfect.DeficientPowerReplayGeneral.Part009

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart045Tree : Tree :=
  .step (.primeLo 3 1151) <|
  .step (.dropHi 4 328) <|
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
              (.step (.dropLo 3 1175) <|
              .step (.dropLo 4 323) <|
              .step (.primeLo 3 1181) <|
              .step (.xLo 325) <|
              .missing 4 163))
            (.step (.primeLo 3 1201) <|
            .splitExp 0 8
              (.step (.grow 0 13) <|
              .missing 0 757)
              (.step (.dropLo 4 319) <|
              .step (.xLo 321) <|
              .splitBase 3 1223
                (.splitExp 1 6
                  (.step (.dropHi 4 323) <|
                  .step (.xHi 321) <|
                  .missing 4 7)
                  (.step (.dropLo 4 322) <|
                  .step (.xLo 325) <|
                  .missing 4 163))
                (.step (.primeLo 3 1229) <|
                .step (.dropHi 4 323) <|
                .step (.xHi 321) <|
                .missing 4 7))))
          (.step (.primeLo 3 1259) <|
          .step (.dropHi 4 321) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 4 312) <|
            .step (.xLo 313) <|
            .splitBase 3 1313
              (.step (.primeHi 3 1307) <|
              .step (.dropLo 4 316) <|
              .step (.xLo 317) <|
              .splitBase 3 1281
                (.step (.primeHi 3 1279) <|
                .splitExp 1 6
                  (.step (.dropHi 4 319) <|
                  .step (.xHi 317) <|
                  .missing 4 53)
                  (.step (.dropLo 4 319) <|
                  .step (.xLo 321) <|
                  .missing 4 7))
                (.step (.primeLo 3 1283) <|
                .step (.dropHi 4 319) <|
                .step (.xHi 317) <|
                .missing 4 53))
              (.step (.primeLo 3 1319) <|
              .step (.dropHi 4 317) <|
              .splitBase 3 1345
                (.step (.primeHi 3 1327) <|
                .step (.dropLo 4 315) <|
                .step (.xLo 317) <|
                .missing 4 53)
                (.step (.primeLo 3 1361) <|
                .step (.dropHi 4 315) <|
                .step (.xHi 313) <|
                .missing 4 157))))))
      (.use 0))

private def deficientFourPowerGeneralPart045Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,1380,1723,2,0⟩, ⟨true,281,325,5,0⟩], 1, deficientFourPowerGeneralPart044⟩]

theorem deficientFourPowerGeneralPart045 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,1150,1723,2,0⟩, ⟨true,257,361,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart045Tree deficientFourPowerGeneralPart045Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart046Tree : Tree :=
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
              (.step (.dropLo 3 1785) <|
              .step (.dropLo 4 295) <|
              .step (.primeLo 3 1787) <|
              .step (.xLo 297) <|
              .missing 4 149))
            (.step (.primeLo 3 1861) <|
            .step (.dropHi 4 296) <|
            .step (.xHi 293) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 1945) <|
              .step (.dropLo 4 292) <|
              .step (.primeLo 3 1949) <|
              .step (.xLo 293) <|
              .missing 4 7)))
          (.step (.primeLo 3 1987) <|
          .step (.dropHi 4 293) <|
          .splitBase 3 2135
            (.step (.primeHi 3 2131) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 4 289) <|
              .splitBase 3 2055
                (.step (.primeHi 3 2053) <|
                .step (.dropLo 4 290) <|
                .step (.xLo 293) <|
                .missing 4 7)
                (.step (.primeLo 3 2063) <|
                .step (.dropHi 4 292) <|
                .step (.xHi 289) <|
                .missing 4 29)))
            (.step (.primeLo 3 2137) <|
            .step (.dropHi 4 290) <|
            .step (.xHi 289) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 2142) <|
              .step (.dropLo 4 286) <|
              .step (.primeLo 3 2143) <|
              .step (.xLo 289) <|
              .missing 4 29)))))
      (.step (.primeLo 3 2311) <|
      .step (.dropHi 4 287) <|
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
              (.step (.dropLo 3 2392) <|
              .step (.dropLo 4 283) <|
              .step (.primeLo 3 2393) <|
              .step (.xLo 285) <|
              .missing 4 11))
            (.step (.primeLo 3 2521) <|
            .step (.dropHi 4 284) <|
            .step (.xHi 281) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 2718) <|
              .step (.dropLo 4 280) <|
              .step (.primeLo 3 2719) <|
              .step (.xLo 281) <|
              .missing 4 47)))
          (.step (.primeLo 3 2777) <|
          .step (.dropHi 4 281) <|
          .splitBase 3 3081
            (.step (.primeHi 3 3079) <|
            .step (.dropLo 4 274) <|
            .step (.xLo 277) <|
            .splitExp 0 8
              (.missing 0 13)
              (.splitBase 3 2919
                (.step (.primeHi 3 2917) <|
                .step (.dropLo 4 279) <|
                .step (.xLo 281) <|
                .missing 4 47)
                (.step (.primeLo 3 2927) <|
                .step (.dropHi 4 280) <|
                .step (.xHi 277) <|
                .missing 4 139)))
            (.step (.primeLo 3 3083) <|
            .step (.dropHi 4 279) <|
            .step (.xHi 277) <|
            .splitExp 0 8
              (.step (.grow 0 13) <|
              .missing 0 757)
              (.step (.dropLo 3 3160) <|
              .step (.dropLo 4 274) <|
              .step (.primeLo 3 3163) <|
              .step (.xLo 277) <|
              .missing 4 139))))))

theorem deficientFourPowerGeneralPart046 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,1733,3465,2,0⟩, ⟨true,225,297,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart046Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart047Tree : Tree :=
  .step (.primeLo 3 4621) <|
  .step (.dropHi 4 270) <|
  .step (.xHi 269) <|
  .splitBase 3 5539
    (.step (.primeHi 3 5531) <|
    .step (.dropLo 4 263) <|
    .step (.xLo 265) <|
    .splitExp 0 8
      (.missing 0 13)
      (.step (.dropLo 3 4793) <|
      .step (.dropLo 4 267) <|
      .step (.xLo 269) <|
      .step (.dropHi 3 5277) <|
      .step (.primeHi 3 5273) <|
      .splitBase 3 5021
        (.splitExp 1 6
          (.step (.dropHi 3 4943) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 3 4911) <|
            .step (.primeLo 3 4919) <|
            .splitBase 3 4929
              (.step (.primeHi 3 4919) <|
              .splitExp 2 4
                (.splitExp 0 12
                  (.reject)
                  (.reject))
                (.reject))
              (.step (.primeLo 3 4931) <|
              .splitExp 2 4
                (.reject)
                (.splitExp 0 12
                  (.reject)
                  (.step (.dropLo 3 4941) <|
                  .step (.primeLo 3 4943) <|
                  .splitExp 0 14
                    (.missing 0 11)
                    (.reject))))))
          (.reject))
        (.step (.primeLo 3 5023) <|
        .splitExp 1 6
          (.reject)
          (.step (.dropLo 3 5093) <|
          .step (.primeLo 3 5099) <|
          .splitExp 0 10
            (.missing 0 23)
            (.step (.dropLo 3 5226) <|
            .step (.primeLo 3 5227) <|
            .splitBase 3 5249
              (.step (.primeHi 3 5237) <|
              .splitExp 2 4
                (.splitExp 0 12
                  (.splitExp 1 8
                    (.missing 1 19)
                    (.reject))
                  (.reject))
                (.reject))
              (.step (.primeLo 3 5261) <|
              .splitExp 2 4
                (.reject)
                (.splitExp 0 12
                  (.reject)
                  (.splitExp 1 8
                    (.missing 1 19)
                    (.reject)))))))))
    (.step (.primeLo 3 5557) <|
    .step (.dropHi 4 268) <|
    .step (.xHi 265) <|
    .splitExp 0 8
      (.missing 0 13)
      (.step (.dropLo 3 6565) <|
      .step (.dropLo 4 264) <|
      .step (.primeLo 3 6569) <|
      .step (.xLo 265) <|
      .missing 4 7))

theorem deficientFourPowerGeneralPart047 : Closed (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,4618,6917,2,0⟩, ⟨true,261,273,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart047Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart048Tree : Tree :=
  .step (.primeLo 3 1733) <|
  .step (.dropHi 4 300) <|
  .step (.xHi 297) <|
  .splitExp 0 6
    (.missing 0 1093)
    (.step (.dropLo 4 223) <|
    .step (.xLo 225) <|
    .splitBase 3 3465
      (.use 0)
      (.step (.primeLo 3 3467) <|
      .step (.dropHi 4 276) <|
      .step (.xHi 273) <|
      .splitExp 1 4
        (.step (.grow 1 11) <|
        .missing 1 71)
        (.step (.dropLo 4 239) <|
        .step (.xLo 241) <|
        .splitBase 3 6933
          (.step (.primeHi 3 6917) <|
          .step (.dropLo 4 248) <|
          .step (.xLo 249) <|
          .splitExp 2 2
            (.missing 2 307)
            (.step (.dropLo 4 261) <|
            .splitBase 3 4617
              (.step (.primeHi 3 4603) <|
              .step (.dropLo 4 266) <|
              .step (.xLo 269) <|
              .splitBase 3 3955
                (.step (.primeHi 3 3947) <|
                .splitExp 0 8
                  (.step (.grow 0 13) <|
                  .missing 0 757)
                  (.step (.dropLo 3 3798) <|
                  .step (.dropLo 4 272) <|
                  .step (.primeLo 3 3803) <|
                  .step (.xLo 273) <|
                  .missing 4 137))
                (.step (.primeLo 3 3967) <|
                .splitExp 0 8
                  (.step (.grow 0 13) <|
                  .missing 0 757)
                  (.splitBase 3 4261
                    (.step (.dropLo 4 270) <|
                    .step (.xLo 273) <|
                    .missing 4 137)
                    (.step (.primeLo 3 4271) <|
                    .step (.dropHi 4 272) <|
                    .step (.xHi 269) <|
                    .reject))))
              (.use 1)))
          (.step (.primeLo 3 6947) <|
          .step (.dropHi 4 265) <|
          .splitExp 2 2
            (.missing 2 307)
            (.step (.dropLo 4 251) <|
            .step (.xLo 253) <|
            .splitBase 3 13893
              (.step (.primeHi 3 13883) <|
              .step (.dropLo 4 256) <|
              .step (.xLo 257) <|
              .splitBase 3 9259
                (.step (.primeHi 3 9257) <|
                .step (.dropLo 4 258) <|
                .step (.xLo 261) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.splitBase 3 7937
                    (.step (.dropLo 4 263) <|
                    .step (.xLo 265) <|
                    .missing 4 7)
                    (.step (.primeLo 3 7949) <|
                    .step (.dropHi 4 264) <|
                    .step (.xHi 261) <|
                    .missing 4 131)))
                (.step (.primeLo 3 9277) <|
                .step (.dropHi 4 263) <|
                .step (.xHi 261) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.step (.dropLo 3 10608) <|
                  .step (.dropLo 4 259) <|
                  .step (.primeLo 3 10613) <|
                  .step (.xLo 261) <|
                  .missing 4 131)))
              (.step (.primeLo 3 13901) <|
              .step (.dropHi 4 260) <|
              .step (.xHi 257) <|
              .splitBase 3 27801
                (.step (.primeHi 3 27799) <|
                .step (.dropLo 4 254) <|
                .step (.xLo 257) <|
                .missing 4 43)
                (.step (.primeLo 3 27803) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.step (.dropLo 3 29063) <|
                  .step (.dropLo 4 254) <|
                  .step (.xLo 257) <|
                  .missing 4 43))))))))

private def deficientFourPowerGeneralPart048Refs : List Known := [
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,1733,3465,2,0⟩, ⟨true,225,297,5,0⟩], 1, deficientFourPowerGeneralPart046⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,4618,6917,2,0⟩, ⟨true,261,273,5,0⟩], 1, deficientFourPowerGeneralPart047⟩]

theorem deficientFourPowerGeneralPart048 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,1726,0,2,0⟩, ⟨true,205,361,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart048Tree deficientFourPowerGeneralPart048Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart049Tree : Tree :=
  .step (.primeLo 3 431) <|
  .step (.dropHi 4 629) <|
  .splitBase 3 861
    (.use 0)
    (.step (.primeLo 3 863) <|
    .step (.dropHi 4 363) <|
    .step (.xHi 361) <|
    .splitBase 3 1725
      (.step (.primeHi 3 1723) <|
      .step (.dropLo 4 232) <|
      .step (.xLo 233) <|
      .splitExp 0 6
        (.step (.fix 0 1093 3) <|
        .step (.dropLo 4 251) <|
        .step (.dropHi 4 289) <|
        .step (.xLo 253) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .missing 1 71)
          (.step (.dropLo 4 272) <|
          .step (.xLo 273) <|
          .splitExp 2 2
            (.missing 2 307)
            (.step (.dropLo 4 288) <|
            .step (.xLo 289) <|
            .missing 4 29)))
        (.step (.dropLo 4 256) <|
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
                        .reject)
                        (.step (.primeLo 3 877) <|
                        .splitExp 1 6
                          (.step (.dropHi 4 359) <|
                          .step (.xHi 357) <|
                          .missing 4 179)
                          (.step (.dropLo 4 359) <|
                          .step (.xLo 361) <|
                          .missing 4 181)))
                      (.step (.primeLo 3 887) <|
                      .step (.dropHi 4 359) <|
                      .step (.xHi 357) <|
                      .splitBase 3 897
                        (.step (.primeHi 3 887) <|
                        .reject)
                        (.step (.primeLo 3 907) <|
                        .step (.dropHi 4 356) <|
                        .step (.xHi 353) <|
                        .missing 4 59))))
                  (.step (.primeLo 3 919) <|
                  .step (.dropHi 4 354) <|
                  .step (.xHi 353) <|
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
                        .step (.dropHi 4 351) <|
                        .step (.xHi 349) <|
                        .missing 4 7))
                      (.step (.primeLo 3 953) <|
                      .step (.dropHi 4 349) <|
                      .splitBase 3 963
                        (.step (.primeHi 3 953) <|
                        .step (.dropLo 4 347) <|
                        .step (.xLo 349) <|
                        .missing 4 7)
                        (.step (.primeLo 3 967) <|
                        .step (.dropHi 4 347) <|
                        .step (.xHi 345) <|
                        .missing 4 173))))))
              (.use 1)))
          (.use 2)))
      (.use 3))

private def deficientFourPowerGeneralPart049Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,431,861,2,0⟩, ⟨true,205,629,5,0⟩], 1, deficientFourPowerGeneralPart042⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,978,1129,2,0⟩, ⟨true,305,361,5,0⟩], 1, deficientFourPowerGeneralPart043⟩,
  ⟨#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,1150,1723,2,0⟩, ⟨true,257,361,5,0⟩], 1, deficientFourPowerGeneralPart045⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,1726,0,2,0⟩, ⟨true,205,361,5,0⟩], 1, deficientFourPowerGeneralPart048⟩]

theorem deficientFourPowerGeneralPart049 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,422,0,2,0⟩, ⟨true,205,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart049Tree deficientFourPowerGeneralPart049Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
