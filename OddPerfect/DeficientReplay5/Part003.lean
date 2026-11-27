module

public import OddPerfect.DeficientReplay5.Part002

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour5Part010Tree : Tree :=
  .step (.primeLo 3 157) <|
  .step (.dropHi 4 244) <|
  .step (.xHi 241) <|
  .splitBase 3 173
    (.step (.dropLo 4 179) <|
    .step (.xLo 181) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 4 193) <|
      .splitBase 3 163
        (.step (.dropLo 4 207) <|
        .step (.xLo 209) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .missing 1 71)
          (.step (.dropLo 4 221) <|
          .splitBase 3 159
            (.step (.primeHi 3 157) <|
            .step (.dropLo 4 233) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 241) <|
              .missing 4 11))
            (.step (.primeLo 3 163) <|
            .step (.dropHi 4 231) <|
            .step (.xHi 229) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 228) <|
              .step (.xLo 229) <|
              .missing 4 23))))
        (.step (.primeLo 3 167) <|
        .step (.dropHi 4 223) <|
        .step (.xHi 221) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .missing 1 71)
          (.step (.dropLo 4 205) <|
          .splitBase 3 169
            (.step (.primeHi 3 167) <|
            .step (.dropLo 4 214) <|
            .step (.xLo 217) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 221) <|
              .missing 4 37))
            (.step (.primeLo 3 173) <|
            .step (.dropHi 4 213) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 211) <|
              .step (.xLo 213) <|
              .missing 4 107))))))
    (.step (.primeLo 3 179) <|
    .step (.dropHi 4 204) <|
    .step (.xHi 201) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 4 173) <|
      .splitExp 1 4
        (.missing 1 11)
        (.step (.dropLo 4 182) <|
        .step (.xLo 185) <|
        .splitBase 3 185
          (.step (.primeHi 3 181) <|
          .step (.dropLo 4 195) <|
          .step (.xLo 197) <|
          .splitExp 2 2
            (.missing 2 127)
            (.step (.dropLo 4 200) <|
            .step (.xLo 201) <|
            .missing 4 101))
          (.step (.primeLo 3 191) <|
          .step (.dropHi 4 191) <|
          .step (.xHi 189) <|
          .splitExp 2 2
            (.missing 2 127)
            (.step (.dropLo 4 187) <|
            .step (.xLo 189) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 192) <|
              .step (.primeLo 3 193) <|
              .splitExp 1 6
                (.reject)
                (.splitExp 0 10
                  (.missing 0 23)
                  (.splitExp 0 12
                    (.reject)
                    (.splitExp 1 8
                      (.missing 1 31)
                      (.splitExp 2 4
                        (.missing 2 151)
                        (.reject)))))))))))

theorem deficientFour5Part010 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,156,193,2,0⟩, ⟨true,161,353,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part010Tree [] _ _ (by decide +kernel)

private def deficientFour5Part011Tree : Tree :=
  .step (.primeLo 3 131) <|
  .step (.dropHi 4 355) <|
  .step (.xHi 353) <|
  .splitBase 3 155
    (.step (.primeHi 3 151) <|
    .step (.dropLo 4 211) <|
    .step (.xLo 213) <|
    .splitBase 3 139
      (.step (.dropLo 4 240) <|
      .step (.xLo 241) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.step (.dropLo 4 265) <|
        .splitBase 3 133
          (.step (.primeHi 3 131) <|
          .step (.dropLo 4 301) <|
          .splitExp 1 4
            (.step (.grow 1 11) <|
            .missing 1 71)
            (.step (.dropLo 4 331) <|
            .step (.xLo 333) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 348) <|
              .step (.xLo 349) <|
              .splitExp 0 8
                (.missing 0 13)
                (.reject))))
          (.step (.primeLo 3 137) <|
          .step (.dropHi 4 317) <|
          .splitExp 1 4
            (.step (.grow 1 11) <|
            .missing 1 71)
            (.step (.dropLo 4 289) <|
            .splitExp 2 2
              (.missing 2 127)
              (.step (.dropLo 4 302) <|
              .step (.xLo 305) <|
              .splitBase 3 137
                (.step (.dropLo 4 312) <|
                .step (.xLo 313) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.step (.dropLo 4 316) <|
                  .step (.xLo 317) <|
                  .missing 4 53))
                (.step (.primeLo 3 139) <|
                .step (.dropHi 4 307) <|
                .step (.xHi 305) <|
                .missing 4 17))))))
      (.step (.primeLo 3 149) <|
      .step (.dropHi 4 267) <|
      .step (.xHi 265) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.step (.dropLo 4 230) <|
        .step (.xLo 233) <|
        .splitExp 1 4
          (.step (.grow 1 11) <|
          .missing 1 71)
          (.step (.dropLo 4 248) <|
          .step (.xLo 249) <|
          .splitExp 2 2
            (.missing 2 127)
            (.step (.dropLo 4 257) <|
            .splitBase 3 149
              (.step (.dropLo 4 263) <|
              .step (.xLo 265) <|
              .missing 4 7)
              (.step (.primeLo 3 151) <|
              .step (.dropHi 4 260) <|
              .step (.xHi 257) <|
              .missing 4 43))))))
    (.use 0)

private def deficientFour5Part011Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,156,193,2,0⟩, ⟨true,161,353,1,1⟩], 1, deficientFour5Part010⟩]

theorem deficientFour5Part011 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,130,193,2,0⟩, ⟨true,161,9213,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part011Tree deficientFour5Part011Refs _ _ (by decide +kernel)

private def deficientFour5Part012Tree : Tree :=
  .step (.primeLo 2 19) <|
  .step (.dropHi 4 9215) <|
  .step (.xHi 9213) <|
  .splitExp 0 4
    (.step (.grow 0 11) <|
    .step (.dropHi 4 235) <|
    .step (.xLo 121) <|
    .step (.xHi 209) <|
    .step (.dropHi 3 157) <|
    .splitBase 3 119
      (.step (.primeHi 3 113) <|
      .step (.dropLo 4 162) <|
      .step (.xLo 165) <|
      .splitBase 3 103
        (.step (.dropLo 4 188) <|
        .step (.xLo 209) <|
        .missing 4 7)
        (.step (.primeLo 3 107) <|
        .step (.dropHi 4 191) <|
        .step (.xHi 165) <|
        .missing 4 83))
      (.step (.primeLo 3 127) <|
      .step (.dropHi 4 148) <|
      .step (.xHi 121) <|
      .missing 4 61))
    (.step (.dropLo 4 161) <|
    .splitBase 3 129
      (.step (.primeHi 3 127) <|
      .step (.dropLo 4 287) <|
      .step (.xLo 289) <|
      .splitBase 3 109
        (.use 0)
        (.step (.primeLo 3 113) <|
        .step (.dropHi 4 631) <|
        .step (.xHi 629) <|
        .splitBase 3 119
          (.step (.primeHi 3 113) <|
          .step (.dropLo 4 399) <|
          .step (.xLo 401) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 476) <|
            .step (.xLo 477) <|
            .splitExp 1 4
              (.step (.grow 1 11) <|
              .missing 1 71)
              (.step (.dropLo 4 558) <|
              .step (.xLo 561) <|
              .splitExp 2 2
                (.missing 2 127)
                (.step (.dropLo 4 607) <|
                .step (.xLo 609) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.step (.dropLo 4 624) <|
                  .step (.xLo 625) <|
                  .splitExp 1 6
                    (.step (.dropHi 4 626) <|
                    .step (.xHi 625) <|
                    .missing 4 313)
                    (.step (.dropLo 4 629) <|
                    .missing 4 7))))))
          (.step (.primeLo 3 127) <|
          .step (.dropHi 4 389) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 324) <|
            .step (.xLo 325) <|
            .splitExp 1 4
              (.step (.grow 1 11) <|
              .missing 1 71)
              (.step (.dropLo 4 360) <|
              .step (.xLo 361) <|
              .splitExp 2 2
                (.step (.dropHi 4 368) <|
                .step (.xHi 365) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.reject))
                (.step (.dropLo 4 380) <|
                .step (.xLo 381) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.step (.dropLo 4 387) <|
                  .step (.xLo 389) <|
                  .missing 4 13)))))))
      (.use 1))

private def deficientFour5Part012Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,109,2,0⟩, ⟨true,289,9213,1,1⟩], 1, deficientFour5Part009⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,130,193,2,0⟩, ⟨true,161,9213,1,1⟩], 1, deficientFour5Part011⟩]

theorem deficientFour5Part012 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,18,19,2,0⟩, ⟨false,97,193,2,0⟩, ⟨true,101,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part012Tree deficientFour5Part012Refs _ _ (by decide +kernel)

private def deficientFour5Part013Tree : Tree :=
  .step (.dropLo 4 1357) <|
  .splitExp 0 6
    (.step (.grow 0 1093) <|
    .step (.xLo 5465) <|
    .step (.dropHi 3 239) <|
    .splitBase 3 223
      (.splitExp 1 4
        (.step (.grow 1 11) <|
        .step (.grow 1 71) <|
        .step (.dropHi 3 222) <|
        .step (.primeHi 3 211) <|
        .step (.xLo 853633) <|
        .splitExp 2 2
          (.step (.grow 2 307) <|
          .reject)
          (.reject))
        (.step (.dropLo 3 218) <|
        .step (.dropLo 4 10716) <|
        .step (.primeLo 3 223) <|
        .step (.xLo 14209) <|
        .splitExp 2 2
          (.step (.grow 2 307) <|
          .reject)
          (.reject)))
      (.step (.primeLo 3 227) <|
      .splitExp 1 4
        (.step (.grow 1 11) <|
        .step (.grow 1 71) <|
        .reject)
        (.splitExp 2 2
          (.step (.grow 2 307) <|
          .step (.dropHi 3 228) <|
          .step (.dropHi 4 6257) <|
          .step (.primeHi 3 227) <|
          .step (.xLo 1006653) <|
          .reject)
          (.step (.dropLo 3 228) <|
          .step (.primeLo 3 229) <|
          .splitBase 3 233
            (.step (.dropLo 4 11940) <|
            .step (.xLo 14209) <|
            .splitBase 3 229
              (.step (.dropLo 4 118143) <|
              .step (.xLo 119137) <|
              .splitExp 1 6
                (.step (.dropHi 4 130263) <|
                .step (.xHi 127881) <|
                .splitExp 2 4
                  (.step (.dropHi 4 119316) <|
                  .step (.xHi 119137) <|
                  .missing 4 71)
                  (.reject))
                (.reject))
              (.step (.primeLo 3 233) <|
              .step (.dropHi 4 14250) <|
              .step (.xHi 14209) <|
              .missing 4 7))
            (.step (.primeLo 3 239) <|
            .step (.dropHi 4 5605) <|
            .step (.xHi 5465) <|
            .missing 4 911)))))
    (.step (.dropLo 3 223) <|
    .step (.dropLo 4 3027) <|
    .step (.xLo 3029) <|
    .splitExp 1 4
      (.step (.grow 1 11) <|
      .step (.grow 1 71) <|
      .step (.xLo 3905) <|
      .splitBase 3 231
        (.step (.primeHi 3 229) <|
        .step (.dropLo 4 8926) <|
        .step (.xLo 10153) <|
        .splitExp 2 2
          (.step (.grow 2 307) <|
          .step (.xLo 719301) <|
          .step (.dropHi 3 225) <|
          .step (.primeHi 3 223) <|
          .reject)
          (.reject))
        (.step (.primeLo 3 233) <|
        .splitExp 2 2
          (.step (.grow 2 307) <|
          .step (.dropHi 3 239) <|
          .step (.dropHi 4 7329) <|
          .step (.xLo 719301) <|
          .reject)
          (.step (.dropLo 4 7842) <|
          .step (.xLo 10153) <|
          .splitBase 3 235
            (.step (.primeHi 3 233) <|
            .reject)
            (.step (.primeLo 3 239) <|
            .step (.dropHi 4 24346) <|
            .step (.xHi 22649) <|
            .splitExp 0 8
              (.step (.grow 0 13) <|
              .missing 0 757)
              (.step (.dropLo 4 12142) <|
              .step (.xLo 13277) <|
              .step (.dropHi 3 240) <|
              .step (.primeHi 3 239) <|
              .step (.dropLo 4 21055) <|
              .step (.xLo 22649) <|
              .missing 4 151)))))
      (.step (.dropLo 3 239) <|
      .step (.dropLo 4 43235) <|
      .step (.xLo 43237) <|
      .splitExp 2 2
        (.step (.grow 2 307) <|
        .step (.xLo 43901) <|
        .splitExp 0 8
          (.step (.grow 0 13) <|
          .step (.grow 0 757) <|
          .step (.xLo 9063561) <|
          .step (.dropHi 3 240) <|
          .step (.primeHi 3 239) <|
          .reject)
          (.reject))
        (.reject)))

theorem deficientFour5Part013 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,211,241,2,0⟩, ⟨true,753,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part013Tree [] _ _ (by decide +kernel)

private def deficientFour5Part014Tree : Tree :=
  .step (.dropLo 4 60755) <|
  .step (.xLo 60757) <|
  .splitExp 0 12
    (.step (.dropHi 4 62947) <|
    .step (.xHi 62945) <|
    .splitExp 1 8
      (.step (.grow 1 19) <|
      .step (.grow 1 31) <|
      .missing 1 829)
      (.step (.dropLo 4 62625) <|
      .splitExp 3 2
        (.step (.grow 3 61) <|
        .missing 3 1087)
        (.step (.dropLo 4 62857) <|
        .splitExp 1 10
          (.step (.dropHi 4 62866) <|
          .step (.xHi 62865) <|
          .splitExp 2 6
            (.reject)
            (.reject))
          (.step (.dropLo 4 62935) <|
          .step (.xLo 62937) <|
          .splitExp 2 6
            (.step (.dropHi 4 62937) <|
            .splitExp 1 12
              (.reject)
              (.reject))
            (.step (.dropLo 4 62945) <|
            .missing 4 13)))))
    (.step (.dropLo 4 62885) <|
    .splitExp 1 8
      (.step (.grow 1 19) <|
      .step (.grow 1 31) <|
      .missing 1 829)
      (.step (.dropLo 4 64891) <|
      .step (.xLo 64893) <|
      .splitExp 0 14
        (.step (.grow 0 11) <|
        .step (.grow 0 13) <|
        .step (.dropHi 4 65237) <|
        .step (.xLo 65065) <|
        .step (.xHi 65065) <|
        .splitExp 3 2
          (.missing 3 61)
          (.reject))
        (.step (.dropLo 4 65153) <|
        .splitExp 3 2
          (.step (.grow 3 61) <|
          .missing 3 1087)
          (.step (.dropLo 4 65404) <|
          .step (.xLo 65405) <|
          .splitExp 1 10
            (.step (.dropHi 4 65447) <|
            .step (.xHi 65445) <|
            .splitExp 0 16
              (.missing 0 1871)
              (.step (.dropLo 4 65434) <|
              .step (.xLo 65437) <|
              .splitExp 2 6
                (.reject)
                (.step (.dropLo 4 65444) <|
                .step (.xLo 65445) <|
                .missing 4 43)))
            (.step (.dropLo 4 65488) <|
            .step (.xLo 65489) <|
            .splitExp 0 16
              (.missing 0 1871)
              (.step (.dropLo 4 65518) <|
              .step (.xLo 65521) <|
              .splitExp 2 6
                (.step (.dropHi 4 65524) <|
                .step (.xHi 65521) <|
                .missing 4 181)
                (.step (.dropLo 4 65528) <|
                .step (.xLo 65529) <|
                .splitExp 0 18
                  (.missing 0 1597)
                  (.step (.dropLo 4 65532) <|
                  .step (.xLo 65533) <|
                  .missing 4 7))))))))

theorem deficientFour5Part014 : Closed (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,58273,65533,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part014Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
