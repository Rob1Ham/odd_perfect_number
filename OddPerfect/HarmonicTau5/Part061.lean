module

public import OddPerfect.HarmonicTau5.Part060
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauRange5_323 : RootRange 5 323 403 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=323) [331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401] [17, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_331
  · exact htauRoot5_337
  · exact htauRoot5_347
  · exact htauRoot5_349
  · exact htauRoot5_353
  · exact htauRoot5_359
  · exact htauRoot5_367
  · exact htauRoot5_373
  · exact htauRoot5_379
  · exact htauRoot5_383
  · exact htauRoot5_389
  · exact htauRoot5_397
  · exact htauRoot5_401

theorem htauRange5_403 : RootRange 5 403 483 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=403) [409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479] [13, 2, 3, 2, 11, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 13, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_409
  · exact htauRoot5_419
  · exact htauRoot5_421
  · exact htauRoot5_431
  · exact htauRoot5_433
  · exact htauRoot5_439
  · exact htauRoot5_443
  · exact htauRoot5_449
  · exact htauRoot5_457
  · exact htauRoot5_461
  · exact htauRoot5_463
  · exact htauRoot5_467
  · exact htauRoot5_479

theorem htauRange5_483 : RootRange 5 483 563 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=483) [487, 491, 499, 503, 509, 521, 523, 541, 547, 557] [3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 23, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 13, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_487
  · exact htauRoot5_491
  · exact htauRoot5_499
  · exact htauRoot5_503
  · exact htauRoot5_509
  · exact htauRoot5_521
  · exact htauRoot5_523
  · exact htauRoot5_541
  · exact htauRoot5_547
  · exact htauRoot5_557

theorem htauRange5_563 : RootRange 5 563 643 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=563) [563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641] [0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_563
  · exact htauRoot5_569
  · exact htauRoot5_571
  · exact htauRoot5_577
  · exact htauRoot5_587
  · exact htauRoot5_593
  · exact htauRoot5_599
  · exact htauRoot5_601
  · exact htauRoot5_607
  · exact htauRoot5_613
  · exact htauRoot5_617
  · exact htauRoot5_619
  · exact htauRoot5_631
  · exact htauRoot5_641

theorem htauRange5_643 : RootRange 5 643 723 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=643) [643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719] [0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 23, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 19, 2, 3, 2, 7, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 7, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_643
  · exact htauRoot5_647
  · exact htauRoot5_653
  · exact htauRoot5_659
  · exact htauRoot5_661
  · exact htauRoot5_673
  · exact htauRoot5_677
  · exact htauRoot5_683
  · exact htauRoot5_691
  · exact htauRoot5_701
  · exact htauRoot5_709
  · exact htauRoot5_719

theorem htauRange5_723 : RootRange 5 723 803 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=723) [727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797] [3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 17, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_727
  · exact htauRoot5_733
  · exact htauRoot5_739
  · exact htauRoot5_743
  · exact htauRoot5_751
  · exact htauRoot5_757
  · exact htauRoot5_761
  · exact htauRoot5_769
  · exact htauRoot5_773
  · exact htauRoot5_787
  · exact htauRoot5_797

theorem htauRange5_803 : RootRange 5 803 883 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=803) [809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881] [11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_809
  · exact htauRoot5_811
  · exact htauRoot5_821
  · exact htauRoot5_823
  · exact htauRoot5_827
  · exact htauRoot5_829
  · exact htauRoot5_839
  · exact htauRoot5_853
  · exact htauRoot5_857
  · exact htauRoot5_859
  · exact htauRoot5_863
  · exact htauRoot5_877
  · exact htauRoot5_881

theorem htauRange5_883 : RootRange 5 883 963 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=883) [883, 887, 907, 911, 919, 929, 937, 941, 947, 953] [0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 29, 2, 17, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 31, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_883
  · exact htauRoot5_887
  · exact htauRoot5_907
  · exact htauRoot5_911
  · exact htauRoot5_919
  · exact htauRoot5_929
  · exact htauRoot5_937
  · exact htauRoot5_941
  · exact htauRoot5_947
  · exact htauRoot5_953

theorem htauRange5_963 : RootRange 5 963 1043 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=963) [967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039] [3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_967
  · exact htauRoot5_971
  · exact htauRoot5_977
  · exact htauRoot5_983
  · exact htauRoot5_991
  · exact htauRoot5_997
  · exact htauRoot5_1009
  · exact htauRoot5_1013
  · exact htauRoot5_1019
  · exact htauRoot5_1021
  · exact htauRoot5_1031
  · exact htauRoot5_1033
  · exact htauRoot5_1039

theorem htauRange5_1043 : RootRange 5 1043 1123 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=1043) [1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117] [7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 29, 2, 5, 2, 3, 2, 13, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 19, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_1049
  · exact htauRoot5_1051
  · exact htauRoot5_1061
  · exact htauRoot5_1063
  · exact htauRoot5_1069
  · exact htauRoot5_1087
  · exact htauRoot5_1091
  · exact htauRoot5_1093
  · exact htauRoot5_1097
  · exact htauRoot5_1103
  · exact htauRoot5_1109
  · exact htauRoot5_1117

theorem htauRange5_1123 : RootRange 5 1123 1203 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=1123) [1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201] [0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 19, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_1123
  · exact htauRoot5_1129
  · exact htauRoot5_1151
  · exact htauRoot5_1153
  · exact htauRoot5_1163
  · exact htauRoot5_1171
  · exact htauRoot5_1181
  · exact htauRoot5_1187
  · exact htauRoot5_1193
  · exact htauRoot5_1201

theorem htauRange5_1203 : RootRange 5 1203 1283 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=1203) [1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279] [3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 11, 2, 3, 2, 29, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 19, 2, 3, 2, 0, 2, 0, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_1213
  · exact htauRoot5_1217
  · exact htauRoot5_1223
  · exact htauRoot5_1229
  · exact htauRoot5_1231
  · exact htauRoot5_1237
  · exact htauRoot5_1249
  · exact htauRoot5_1259
  · exact htauRoot5_1277
  · exact htauRoot5_1279

theorem htauRange5_1283 : RootRange 5 1283 1363 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=1283) [1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361] [0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 31, 2, 3, 2, 7, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_1283
  · exact htauRoot5_1289
  · exact htauRoot5_1291
  · exact htauRoot5_1297
  · exact htauRoot5_1301
  · exact htauRoot5_1303
  · exact htauRoot5_1307
  · exact htauRoot5_1319
  · exact htauRoot5_1321
  · exact htauRoot5_1327
  · exact htauRoot5_1361

theorem htauRange5_1363 : RootRange 5 1363 1443 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=1363) [1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439] [29, 2, 3, 2, 0, 2, 37, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 0, 2, 3, 2, 23, 2, 5, 2, 3, 2, 0, 2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 11, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_1367
  · exact htauRoot5_1373
  · exact htauRoot5_1381
  · exact htauRoot5_1399
  · exact htauRoot5_1409
  · exact htauRoot5_1423
  · exact htauRoot5_1427
  · exact htauRoot5_1429
  · exact htauRoot5_1433
  · exact htauRoot5_1439

theorem htauRange5_1443 : RootRange 5 1443 1523 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=1443) [1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511] [3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 31, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 17, 2, 3, 2, 37, 2, 7, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_1447
  · exact htauRoot5_1451
  · exact htauRoot5_1453
  · exact htauRoot5_1459
  · exact htauRoot5_1471
  · exact htauRoot5_1481
  · exact htauRoot5_1483
  · exact htauRoot5_1487
  · exact htauRoot5_1489
  · exact htauRoot5_1493
  · exact htauRoot5_1499
  · exact htauRoot5_1511

theorem htauRange5_1523 : RootRange 5 1523 1603 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=1523) [1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601] [0, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 29, 2, 3, 2, 23, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_1523
  · exact htauRoot5_1531
  · exact htauRoot5_1543
  · exact htauRoot5_1549
  · exact htauRoot5_1553
  · exact htauRoot5_1559
  · exact htauRoot5_1567
  · exact htauRoot5_1571
  · exact htauRoot5_1579
  · exact htauRoot5_1583
  · exact htauRoot5_1597
  · exact htauRoot5_1601

theorem htauRange5_1603 : RootRange 5 1603 1683 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=1603) [1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669] [7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 23, 2, 3, 2, 0, 2, 11, 2, 3, 2, 31, 2, 5, 2, 3, 2, 17, 2, 13, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 41, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_1607
  · exact htauRoot5_1609
  · exact htauRoot5_1613
  · exact htauRoot5_1619
  · exact htauRoot5_1621
  · exact htauRoot5_1627
  · exact htauRoot5_1637
  · exact htauRoot5_1657
  · exact htauRoot5_1663
  · exact htauRoot5_1667
  · exact htauRoot5_1669

theorem htauRange5_1683 : RootRange 5 1683 1763 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=1683) [1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759] [3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 17, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 37, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 17, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_1693
  · exact htauRoot5_1697
  · exact htauRoot5_1699
  · exact htauRoot5_1709
  · exact htauRoot5_1721
  · exact htauRoot5_1723
  · exact htauRoot5_1733
  · exact htauRoot5_1741
  · exact htauRoot5_1747
  · exact htauRoot5_1753
  · exact htauRoot5_1759

theorem htauRange5_1763 : RootRange 5 1763 1843 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=1763) [1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831] [41, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 23, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 31, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_1777
  · exact htauRoot5_1783
  · exact htauRoot5_1787
  · exact htauRoot5_1789
  · exact htauRoot5_1801
  · exact htauRoot5_1811
  · exact htauRoot5_1823
  · exact htauRoot5_1831

theorem htauRange5_1843 : RootRange 5 1843 1923 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=1843) [1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913] [19, 2, 3, 2, 0, 2, 43, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 23, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 17, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_1847
  · exact htauRoot5_1861
  · exact htauRoot5_1867
  · exact htauRoot5_1871
  · exact htauRoot5_1873
  · exact htauRoot5_1877
  · exact htauRoot5_1879
  · exact htauRoot5_1889
  · exact htauRoot5_1901
  · exact htauRoot5_1907
  · exact htauRoot5_1913

theorem htauRange5_1923 : RootRange 5 1923 2003 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=1923) [1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999] [3, 2, 5, 2, 41, 2, 3, 2, 0, 2, 0, 2, 3, 2, 13, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 19, 2, 3, 2, 37, 2, 13, 2, 3, 2, 7, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_1931
  · exact htauRoot5_1933
  · exact htauRoot5_1949
  · exact htauRoot5_1951
  · exact htauRoot5_1973
  · exact htauRoot5_1979
  · exact htauRoot5_1987
  · exact htauRoot5_1993
  · exact htauRoot5_1997
  · exact htauRoot5_1999

theorem htauRange5_2003 : RootRange 5 2003 2083 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=2003) [2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081] [0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 43, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 0, 2, 3, 2, 11, 2, 29, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 31, 2, 3, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_2003
  · exact htauRoot5_2011
  · exact htauRoot5_2017
  · exact htauRoot5_2027
  · exact htauRoot5_2029
  · exact htauRoot5_2039
  · exact htauRoot5_2053
  · exact htauRoot5_2063
  · exact htauRoot5_2069
  · exact htauRoot5_2081

theorem htauRange5_2083 : RootRange 5 2083 2163 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=2083) [2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161] [0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 29, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 19, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_2083
  · exact htauRoot5_2087
  · exact htauRoot5_2089
  · exact htauRoot5_2099
  · exact htauRoot5_2111
  · exact htauRoot5_2113
  · exact htauRoot5_2129
  · exact htauRoot5_2131
  · exact htauRoot5_2137
  · exact htauRoot5_2141
  · exact htauRoot5_2143
  · exact htauRoot5_2153
  · exact htauRoot5_2161

theorem htauRange5_2163 : RootRange 5 2163 2243 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=2163) [2179, 2203, 2207, 2213, 2221, 2237, 2239] [3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 41, 2, 3, 2, 7, 2, 0, 2, 3, 2, 37, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 31, 2, 0, 2, 3, 2, 0, 2, 47, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 0, 2, 3, 2, 5, 2, 17, 2, 3, 2, 23, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_2179
  · exact htauRoot5_2203
  · exact htauRoot5_2207
  · exact htauRoot5_2213
  · exact htauRoot5_2221
  · exact htauRoot5_2237
  · exact htauRoot5_2239

theorem htauRange5_2243 : RootRange 5 2243 2323 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=2243) [2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311] [0, 2, 5, 2, 3, 2, 13, 2, 0, 2, 3, 2, 5, 2, 37, 2, 3, 2, 7, 2, 31, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 43, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 29, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_2243
  · exact htauRoot5_2251
  · exact htauRoot5_2267
  · exact htauRoot5_2269
  · exact htauRoot5_2273
  · exact htauRoot5_2281
  · exact htauRoot5_2287
  · exact htauRoot5_2293
  · exact htauRoot5_2297
  · exact htauRoot5_2309
  · exact htauRoot5_2311

theorem htauRange5_2323 : RootRange 5 2323 2403 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=2323) [2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399] [23, 2, 3, 2, 13, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 23, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 7, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_2333
  · exact htauRoot5_2339
  · exact htauRoot5_2341
  · exact htauRoot5_2347
  · exact htauRoot5_2351
  · exact htauRoot5_2357
  · exact htauRoot5_2371
  · exact htauRoot5_2377
  · exact htauRoot5_2381
  · exact htauRoot5_2383
  · exact htauRoot5_2389
  · exact htauRoot5_2393
  · exact htauRoot5_2399

theorem htauRange5_2403 : RootRange 5 2403 2483 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=2403) [2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477] [3, 2, 5, 2, 29, 2, 3, 2, 0, 2, 19, 2, 3, 2, 0, 2, 41, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 23, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 37, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_2411
  · exact htauRoot5_2417
  · exact htauRoot5_2423
  · exact htauRoot5_2437
  · exact htauRoot5_2441
  · exact htauRoot5_2447
  · exact htauRoot5_2459
  · exact htauRoot5_2467
  · exact htauRoot5_2473
  · exact htauRoot5_2477

theorem htauRange5_2483 : RootRange 5 2483 2563 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=2483) [2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557] [13, 2, 5, 2, 3, 2, 19, 2, 47, 2, 3, 2, 5, 2, 11, 2, 3, 2, 41, 2, 0, 2, 3, 2, 23, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 17, 2, 3, 2, 43, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 13, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_2503
  · exact htauRoot5_2521
  · exact htauRoot5_2531
  · exact htauRoot5_2539
  · exact htauRoot5_2543
  · exact htauRoot5_2549
  · exact htauRoot5_2551
  · exact htauRoot5_2557

theorem htauRange5_2563 : RootRange 5 2563 2643 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=2563) [2579, 2591, 2593, 2609, 2617, 2621, 2633] [11, 2, 3, 2, 17, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 0, 2, 29, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 23, 2, 3, 2, 19, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 43, 2, 3, 2, 37, 2, 11, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 19, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_2579
  · exact htauRoot5_2591
  · exact htauRoot5_2593
  · exact htauRoot5_2609
  · exact htauRoot5_2617
  · exact htauRoot5_2621
  · exact htauRoot5_2633

theorem htauRange5_2643 : RootRange 5 2643 2723 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=2643) [2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719] [3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 37, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 0, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_2647
  · exact htauRoot5_2657
  · exact htauRoot5_2659
  · exact htauRoot5_2663
  · exact htauRoot5_2671
  · exact htauRoot5_2677
  · exact htauRoot5_2683
  · exact htauRoot5_2687
  · exact htauRoot5_2689
  · exact htauRoot5_2693
  · exact htauRoot5_2699
  · exact htauRoot5_2707
  · exact htauRoot5_2711
  · exact htauRoot5_2713
  · exact htauRoot5_2719

end OddPerfect.HarmonicChain
