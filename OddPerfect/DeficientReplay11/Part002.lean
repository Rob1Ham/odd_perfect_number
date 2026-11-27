module

public import OddPerfect.DeficientReplay11.Part001

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour11Part005Tree : Tree :=
  .step (.primeLo 3 281) <|
  .splitExp 0 4
    (.step (.dropHi 2 94) <|
    .step (.dropHi 3 348) <|
    .step (.primeHi 3 347) <|
    .step (.primeHi 2 89) <|
    .splitExp 1 2
      (.missing 1 7)
      (.reject))
    (.splitBase 2 105
      (.step (.primeHi 2 103) <|
      .step (.dropLo 3 665) <|
      .step (.primeLo 3 673) <|
      .splitBase 2 95
        (.step (.primeHi 2 89) <|
        .reject)
        (.step (.primeLo 2 97) <|
        .splitBase 3 1345
          (.step (.primeHi 3 1327) <|
          .splitExp 1 2
            (.missing 1 7)
            (.step (.dropLo 2 102) <|
            .step (.dropLo 3 1318) <|
            .step (.primeLo 2 103) <|
            .step (.primeLo 3 1319) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.reject)))
          (.step (.primeLo 3 1361) <|
          .splitExp 1 2
            (.missing 1 7)
            (.splitBase 3 2721
              (.step (.primeHi 3 2719) <|
              .step (.dropLo 2 99) <|
              .step (.primeLo 2 101) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.reject))
              (.use 0)))))
      (.step (.primeLo 2 107) <|
      .step (.dropHi 3 1514) <|
      .step (.primeHi 3 1511) <|
      .splitBase 3 473
        (.use 1)
        (.step (.primeLo 3 479) <|
        .step (.dropHi 2 126) <|
        .step (.primeHi 2 113) <|
        .splitBase 3 727
          (.splitExp 1 2
            (.missing 1 7)
            (.step (.dropLo 2 109) <|
            .step (.dropLo 3 615) <|
            .step (.primeLo 3 617) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.reject)))
          (.step (.primeLo 3 733) <|
          .splitExp 1 2
            (.missing 1 7)
            (.splitBase 3 987
              (.step (.primeHi 3 983) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 2 110) <|
                .step (.dropLo 3 820) <|
                .step (.primeLo 2 113) <|
                .step (.primeLo 3 821) <|
                .step (.dropHi 3 861) <|
                .step (.primeHi 3 859) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.step (.dropLo 3 852) <|
                  .step (.primeLo 3 853) <|
                  .splitExp 1 4
                    (.step (.grow 1 5) <|
                    .step (.dropHi 3 856) <|
                    .step (.primeHi 3 853) <|
                    .splitExp 0 10
                      (.missing 0 23)
                      (.reject))
                    (.step (.dropLo 3 856) <|
                    .step (.primeLo 3 857) <|
                    .splitExp 0 10
                      (.missing 0 23)
                      (.reject)))))
              (.use 2))))))

private def deficientFour11Part005Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,2722,0,2,0⟩, ⟨true,5,5,1,1⟩], 1, deficientFour11Part002⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,11,11,2,0⟩, ⟨false,107,131,2,0⟩, ⟨false,281,473,2,0⟩, ⟨true,5,5,1,1⟩], 1, deficientFour11Part003⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,988,1511,2,0⟩, ⟨true,5,5,1,1⟩], 1, deficientFour11Part004⟩]

theorem deficientFour11Part005 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,89,131,2,0⟩, ⟨false,278,0,2,0⟩, ⟨true,5,5,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour11Part005Tree deficientFour11Part005Refs _ _ (by decide +kernel)

private def deficientFour11Part006Tree : Tree :=
  .step (.primeLo 3 269) <|
  .step (.dropHi 2 158) <|
  .step (.primeHi 2 157) <|
  .splitExp 1 2
    (.missing 1 7)
    (.splitBase 3 309
      (.step (.primeHi 3 307) <|
      .step (.dropLo 2 138) <|
      .step (.primeLo 2 139) <|
      .splitBase 2 147
        (.step (.primeHi 2 139) <|
        .step (.dropLo 3 304) <|
        .step (.primeLo 3 307) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.reject))
        (.step (.primeLo 2 149) <|
        .step (.dropHi 3 302) <|
        .step (.primeHi 3 293) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 2 150) <|
          .step (.primeLo 2 151) <|
          .splitBase 3 279
            (.step (.primeHi 3 277) <|
            .step (.dropLo 2 154) <|
            .step (.primeLo 2 157) <|
            .step (.dropHi 3 273) <|
            .step (.primeHi 3 271) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject))
            (.step (.primeLo 3 281) <|
            .step (.dropHi 2 154) <|
            .step (.primeHi 2 151) <|
            .step (.dropLo 3 289) <|
            .step (.primeLo 3 293) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject)))))
      (.step (.primeLo 3 311) <|
      .step (.dropHi 2 146) <|
      .step (.primeHi 2 139) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.step (.dropLo 3 346) <|
        .step (.primeLo 3 347) <|
        .splitBase 3 355
          (.step (.primeHi 3 353) <|
          .step (.dropLo 2 138) <|
          .step (.primeLo 2 139) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 3 352) <|
            .step (.primeLo 3 353) <|
            .splitExp 1 4
              (.step (.grow 1 5) <|
              .splitExp 0 10
                (.missing 0 23)
                (.splitExp 0 12
                  (.reject)
                  (.reject)))
              (.reject)))
          (.step (.primeLo 3 359) <|
          .step (.dropHi 2 138) <|
          .step (.primeHi 2 137) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 3 365) <|
            .step (.primeLo 3 367) <|
            .splitExp 1 4
              (.step (.grow 1 5) <|
              .reject)
              (.splitExp 0 10
                (.missing 0 23)
                (.reject)))))))

theorem deficientFour11Part006 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,11,11,2,0⟩, ⟨false,137,181,2,0⟩, ⟨false,268,367,2,0⟩, ⟨true,5,5,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour11Part006Tree [] _ _ (by decide +kernel)

private def deficientFour11Part007Tree : Tree :=
  .splitBase 3 201
    (.step (.primeHi 3 199) <|
    .step (.primeHi 2 197) <|
    .step (.dropLo 2 161) <|
    .step (.dropLo 3 162) <|
    .step (.primeLo 2 163) <|
    .step (.primeLo 3 167) <|
    .splitBase 2 177
      (.step (.primeHi 2 173) <|
      .step (.dropLo 3 183) <|
      .step (.primeLo 3 191) <|
      .splitExp 1 2
        (.missing 1 7)
        (.reject))
      (.step (.primeLo 2 179) <|
      .step (.primeLo 3 181) <|
      .splitExp 1 2
        (.missing 1 7)
        (.step (.dropLo 2 183) <|
        .step (.dropLo 3 184) <|
        .step (.primeLo 2 191) <|
        .step (.primeLo 3 193) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.reject))))
    (.step (.primeLo 3 211) <|
    .step (.dropHi 2 189) <|
    .step (.primeHi 2 181) <|
    .splitBase 3 267
      (.step (.primeHi 3 263) <|
      .splitBase 2 155
        (.step (.primeHi 2 151) <|
        .step (.dropLo 3 217) <|
        .step (.primeLo 3 223) <|
        .splitExp 1 2
          (.missing 1 7)
          (.step (.dropLo 2 149) <|
          .step (.dropLo 3 258) <|
          .step (.primeLo 3 263) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.reject)))
        (.step (.primeLo 2 157) <|
        .splitExp 1 2
          (.missing 1 7)
          (.splitBase 3 233
            (.step (.dropLo 2 161) <|
            .step (.primeLo 2 163) <|
            .splitBase 2 171
              (.step (.primeHi 2 167) <|
              .step (.dropLo 3 222) <|
              .step (.primeLo 3 223) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.reject))
              (.step (.primeLo 2 173) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 3 219) <|
                .step (.primeLo 3 223) <|
                .step (.dropHi 2 180) <|
                .step (.primeHi 2 179) <|
                .splitBase 2 175
                  (.step (.primeHi 2 173) <|
                  .step (.dropLo 3 232) <|
                  .step (.primeLo 3 233) <|
                  .splitExp 0 8
                    (.missing 0 13)
                    (.reject))
                  (.step (.primeLo 2 179) <|
                  .step (.dropHi 3 225) <|
                  .step (.primeHi 3 223) <|
                  .splitExp 0 8
                    (.missing 0 13)
                    (.reject)))))
            (.step (.primeLo 3 239) <|
            .step (.dropHi 2 171) <|
            .step (.primeHi 2 167) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.step (.dropLo 2 159) <|
              .step (.dropLo 3 244) <|
              .step (.primeLo 2 163) <|
              .step (.primeLo 3 251) <|
              .step (.dropHi 2 165) <|
              .step (.dropHi 3 257) <|
              .step (.primeHi 2 163) <|
              .step (.dropLo 3 253) <|
              .step (.primeLo 3 257) <|
              .splitExp 0 8
                (.missing 0 13)
                (.splitExp 1 4
                  (.step (.grow 1 5) <|
                  .reject)
                  (.splitExp 0 10
                    (.missing 0 23)
                    (.reject))))))))
      (.use 0))

private def deficientFour11Part007Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,11,11,2,0⟩, ⟨false,137,181,2,0⟩, ⟨false,268,367,2,0⟩, ⟨true,5,5,1,1⟩], 1, deficientFour11Part006⟩]

theorem deficientFour11Part007 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,11,11,2,0⟩, ⟨false,137,353,2,0⟩, ⟨false,139,367,2,0⟩, ⟨true,5,5,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour11Part007Tree deficientFour11Part007Refs _ _ (by decide +kernel)

private def closedSecond11Tree : Tree :=
  .step (.primeLo 2 13) <|
  .step (.primeLo 3 17) <|
  .step (.dropHi 4 18) <|
  .step (.xHi 17) <|
  .splitBase 2 25
    (.step (.primeHi 2 23) <|
    .splitBase 3 33
      (.step (.primeHi 3 31) <|
      .step (.dropLo 4 7) <|
      .step (.xLo 9) <|
      .splitExp 0 2
        (.step (.dropHi 2 16) <|
        .step (.dropHi 3 22) <|
        .step (.dropHi 4 10) <|
        .step (.primeHi 3 19) <|
        .step (.primeHi 2 13) <|
        .step (.xHi 9) <|
        .missing 4 5)
        (.splitBase 2 15
          (.step (.primeHi 2 13) <|
          .step (.dropLo 4 12) <|
          .step (.xLo 13) <|
          .step (.dropHi 3 26) <|
          .step (.primeHi 3 23) <|
          .step (.dropLo 4 14) <|
          .step (.xLo 17) <|
          .step (.dropHi 3 18) <|
          .step (.primeHi 3 17) <|
          .splitExp 0 4
            (.splitExp 1 2
              (.missing 1 7)
              (.reject))
            (.reject))
          (.step (.primeLo 2 17) <|
          .step (.primeLo 3 19) <|
          .step (.dropHi 4 12) <|
          .step (.xHi 9) <|
          .missing 4 5)))
      (.step (.primeLo 3 37) <|
      .step (.dropHi 4 11) <|
      .step (.xHi 9) <|
      .splitExp 0 2
        (.step (.fix 0 13 2) <|
        .step (.dropLo 4 7) <|
        .step (.dropHi 4 7) <|
        .step (.xLo 9) <|
        .reject)
        (.step (.dropLo 4 7) <|
        .step (.xLo 9) <|
        .missing 4 5)))
    (.step (.primeLo 2 29) <|
    .step (.primeLo 3 31) <|
    .step (.dropHi 4 7) <|
    .step (.xHi 5) <|
    .splitExp 0 2
      (.missing 0 13)
      (.step (.dropLo 2 67) <|
      .step (.dropLo 3 67) <|
      .step (.primeLo 3 71) <|
      .splitBase 2 133
        (.step (.primeHi 2 131) <|
        .step (.dropLo 3 138) <|
        .step (.primeLo 3 139) <|
        .splitBase 2 87
          (.use 0)
          (.step (.primeLo 2 89) <|
          .splitBase 3 277
            (.splitExp 0 4
              (.splitBase 2 105
                (.step (.primeHi 2 103) <|
                .step (.dropLo 3 193) <|
                .splitBase 3 227
                  (.step (.dropLo 2 95) <|
                  .step (.primeLo 2 97) <|
                  .splitExp 1 2
                    (.missing 1 7)
                    (.step (.dropLo 2 102) <|
                    .step (.dropLo 3 226) <|
                    .step (.primeLo 2 103) <|
                    .step (.primeLo 3 227) <|
                    .reject))
                  (.step (.primeLo 3 229) <|
                  .step (.dropHi 2 102) <|
                  .step (.primeHi 2 101) <|
                  .splitBase 2 93
                    (.step (.primeHi 2 89) <|
                    .step (.dropLo 3 276) <|
                    .step (.primeLo 3 277) <|
                    .splitExp 1 2
                      (.missing 1 7)
                      (.reject))
                    (.step (.primeLo 2 97) <|
                    .step (.dropHi 3 262) <|
                    .step (.primeHi 3 257) <|
                    .splitExp 1 2
                      (.missing 1 7)
                      (.step (.dropLo 3 236) <|
                      .step (.primeLo 3 239) <|
                      .step (.dropHi 2 100) <|
                      .step (.primeHi 2 97) <|
                      .reject))))
                (.step (.primeLo 2 107) <|
                .step (.dropHi 3 209) <|
                .step (.primeHi 3 199) <|
                .splitBase 3 163
                  (.step (.dropLo 2 114) <|
                  .step (.primeLo 2 127) <|
                  .step (.dropHi 3 160) <|
                  .step (.primeHi 3 157) <|
                  .splitExp 1 2
                    (.missing 1 7)
                    (.step (.dropLo 2 128) <|
                    .step (.dropLo 3 153) <|
                    .step (.primeLo 2 131) <|
                    .step (.primeLo 3 157) <|
                    .reject))
                  (.step (.primeLo 3 167) <|
                  .step (.dropHi 2 122) <|
                  .step (.primeHi 2 113) <|
                  .splitExp 1 2
                    (.missing 1 7)
                    (.step (.dropLo 2 109) <|
                    .step (.dropLo 3 189) <|
                    .step (.primeLo 3 191) <|
                    .step (.dropHi 2 112) <|
                    .step (.primeHi 2 109) <|
                    .reject))))
              (.reject))
            (.use 1)))
        (.step (.primeLo 2 137) <|
        .step (.primeLo 3 139) <|
        .step (.dropHi 2 353) <|
        .step (.dropHi 3 367) <|
        .splitExp 0 4
          (.step (.dropHi 2 144) <|
          .step (.dropHi 3 146) <|
          .step (.primeHi 3 139) <|
          .step (.primeHi 2 137) <|
          .splitExp 1 2
            (.missing 1 7)
            (.reject))
          (.use 2))))

private def closedSecond11Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,67,87,2,0⟩, ⟨false,139,0,2,0⟩, ⟨true,5,5,1,1⟩], 1, deficientFour11Part000⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,89,131,2,0⟩, ⟨false,278,0,2,0⟩, ⟨true,5,5,1,1⟩], 1, deficientFour11Part005⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,11,11,2,0⟩, ⟨false,137,353,2,0⟩, ⟨false,139,367,2,0⟩, ⟨true,5,5,1,1⟩], 1, deficientFour11Part007⟩]

theorem closedSecond11 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,5,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound closedSecond11Tree closedSecond11Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
