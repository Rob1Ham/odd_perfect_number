module

public import OddPerfect.IndexRange343

public section

namespace OddPerfect.IndexSieve

private theorem exactValid_of_all {rows : List Row}
    (h : rows.all Row.fastExactValidBool = true) :
    ∀ z : Fin rows.length, (rows.get z).exactValid := fun z =>
  (Row.fastExactValidBool_eq _).mp (List.all_eq_true.mp h _ (List.get_mem rows z))

private def rows_511 : List Row := [
  ⟨513,3,19⟩, ⟨531,59,59⟩, ⟨539,7,11⟩, ⟨549,3,3⟩, ⟨555,3,5⟩, ⟨561,11,11⟩,
  ⟨567,3,3⟩, ⟨575,5,5⟩, ⟨585,5,5⟩, ⟨595,5,5⟩, ⟨603,3,3⟩, ⟨605,5,5⟩,
  ⟨609,3,7⟩, ⟨615,3,5⟩, ⟨621,3,23⟩, ⟨627,3,11⟩, ⟨637,13,13⟩, ⟨639,71,71⟩,
  ⟨645,3,5⟩, ⟨651,3,7⟩, ⟨657,3,3⟩]

set_option maxRecDepth 30000 in
private theorem rows_511_valid : ∀ z : Fin rows_511.length, (rows_511.get z).exactValid := exactValid_of_all (by decide +kernel)

set_option maxRecDepth 30000 in
private theorem covers_511_661 : Covers 511 661 :=
  covers_of_table rows_511 rows_511_valid (by decide +kernel)

private def rows_661 : List Row := [
  ⟨663,13,17⟩, ⟨665,5,7⟩, ⟨675,5,5⟩, ⟨693,7,11⟩, ⟨705,5,5⟩, ⟨711,3,3⟩,
  ⟨715,5,11⟩, ⟨725,29,29⟩, ⟨741,13,19⟩, ⟨747,83,83⟩, ⟨759,11,11⟩, ⟨765,3,5⟩,
  ⟨775,5,31⟩, ⟨777,3,7⟩, ⟨783,3,29⟩, ⟨795,3,5⟩, ⟨801,89,89⟩, ⟨805,5,5⟩]

set_option maxRecDepth 30000 in
private theorem rows_661_valid : ∀ z : Fin rows_661.length, (rows_661.get z).exactValid := exactValid_of_all (by decide +kernel)

set_option maxRecDepth 30000 in
private theorem covers_661_811 : Covers 661 811 :=
  covers_of_table rows_661 rows_661_valid (by decide +kernel)

private def rows_811 : List Row := [
  ⟨819,7,13⟩, ⟨825,3,5⟩, ⟨833,17,17⟩, ⟨837,3,31⟩, ⟨845,5,5⟩, ⟨847,7,11⟩,
  ⟨855,3,5⟩, ⟨861,3,41⟩, ⟨867,3,3⟩, ⟨873,3,3⟩, ⟨875,5,5⟩, ⟨885,3,5⟩,
  ⟨891,11,11⟩, ⟨897,13,23⟩, ⟨903,3,7⟩, ⟨909,101,101⟩, ⟨915,3,5⟩, ⟨925,37,37⟩,
  ⟨927,3,3⟩, ⟨931,19,19⟩, ⟨935,5,5⟩, ⟨957,11,11⟩]

set_option maxRecDepth 30000 in
private theorem rows_811_valid : ∀ z : Fin rows_811.length, (rows_811.get z).exactValid := exactValid_of_all (by decide +kernel)

set_option maxRecDepth 30000 in
private theorem covers_811_961 : Covers 811 961 :=
  covers_of_table rows_811 rows_811_valid (by decide +kernel)

private def rows_961 : List Row := [
  ⟨963,107,107⟩, ⟨969,3,17⟩, ⟨975,5,5⟩, ⟨981,3,3⟩, ⟨987,47,47⟩, ⟨999,3,37⟩,
  ⟨1001,7,13⟩, ⟨1005,3,5⟩, ⟨1015,5,5⟩, ⟨1017,113,113⟩, ⟨1023,11,11⟩, ⟨1025,5,5⟩,
  ⟨1029,3,7⟩, ⟨1035,5,5⟩, ⟨1045,5,11⟩, ⟨1053,3,3⟩, ⟨1065,3,5⟩, ⟨1071,3,17⟩,
  ⟨1075,43,43⟩, ⟨1083,3,3⟩, ⟨1085,5,31⟩, ⟨1095,3,5⟩, ⟨1105,5,5⟩, ⟨1107,3,41⟩]

set_option maxRecDepth 30000 in
private theorem rows_961_valid : ∀ z : Fin rows_961.length, (rows_961.get z).exactValid := exactValid_of_all (by decide +kernel)

set_option maxRecDepth 30000 in
private theorem covers_961_1111 : Covers 961 1111 :=
  covers_of_table rows_961 rows_961_valid (by decide +kernel)

private def rows_1111 : List Row := [
  ⟨1113,3,7⟩, ⟨1125,3,3⟩, ⟨1127,7,23⟩, ⟨1131,13,29⟩, ⟨1143,3,3⟩, ⟨1161,3,43⟩,
  ⟨1173,17,23⟩, ⟨1175,47,47⟩, ⟨1179,131,131⟩, ⟨1183,7,13⟩, ⟨1185,3,5⟩, ⟨1197,3,19⟩,
  ⟨1209,3,31⟩, ⟨1215,5,5⟩, ⟨1221,11,11⟩, ⟨1233,137,137⟩, ⟨1235,13,19⟩, ⟨1239,3,7⟩,
  ⟨1245,5,5⟩, ⟨1251,3,3⟩]

set_option maxRecDepth 30000 in
private theorem rows_1111_valid : ∀ z : Fin rows_1111.length, (rows_1111.get z).exactValid := exactValid_of_all (by decide +kernel)

set_option maxRecDepth 30000 in
private theorem covers_1111_1261 : Covers 1111 1261 :=
  covers_of_table rows_1111 rows_1111_valid (by decide +kernel)

private def rows_1261 : List Row := [
  ⟨1265,5,5⟩, ⟨1269,47,47⟩, ⟨1275,3,5⟩, ⟨1281,3,7⟩, ⟨1287,11,13⟩, ⟨1295,5,5⟩,
  ⟨1305,3,5⟩, ⟨1309,7,17⟩, ⟨1311,19,23⟩, ⟨1323,3,3⟩, ⟨1325,53,53⟩, ⟨1331,11,11⟩,
  ⟨1335,3,5⟩, ⟨1341,149,149⟩, ⟨1353,11,11⟩, ⟨1359,3,3⟩, ⟨1375,5,5⟩, ⟨1377,17,17⟩,
  ⟨1395,3,31⟩, ⟨1407,3,7⟩]

set_option maxRecDepth 30000 in
private theorem rows_1261_valid : ∀ z : Fin rows_1261.length, (rows_1261.get z).exactValid := exactValid_of_all (by decide +kernel)

set_option maxRecDepth 30000 in
private theorem covers_1261_1411 : Covers 1261 1411 :=
  covers_of_table rows_1261 rows_1261_valid (by decide +kernel)

private def rows_1411 : List Row := [
  ⟨1413,3,3⟩, ⟨1419,3,43⟩, ⟨1421,7,29⟩, ⟨1425,3,5⟩, ⟨1431,53,53⟩, ⟨1435,5,5⟩,
  ⟨1443,3,37⟩, ⟨1445,5,5⟩, ⟨1449,3,7⟩, ⟨1455,3,5⟩, ⟨1463,7,19⟩, ⟨1467,3,3⟩,
  ⟨1475,59,59⟩, ⟨1479,3,17⟩, ⟨1485,3,5⟩, ⟨1491,3,7⟩, ⟨1495,5,5⟩, ⟨1503,3,3⟩,
  ⟨1505,5,5⟩, ⟨1515,3,5⟩, ⟨1519,31,31⟩, ⟨1525,5,5⟩, ⟨1533,3,7⟩, ⟨1539,3,3⟩,
  ⟨1545,3,5⟩, ⟨1547,7,13⟩, ⟨1551,11,11⟩, ⟨1557,173,173⟩]

set_option maxRecDepth 30000 in
private theorem rows_1411_valid : ∀ z : Fin rows_1411.length, (rows_1411.get z).exactValid := exactValid_of_all (by decide +kernel)

set_option maxRecDepth 30000 in
private theorem covers_1411_1561 : Covers 1411 1561 :=
  covers_of_table rows_1411 rows_1411_valid (by decide +kernel)

private def rows_1561 : List Row := [
  ⟨1573,13,13⟩, ⟨1581,3,17⟩, ⟨1587,3,3⟩, ⟨1593,3,59⟩, ⟨1595,5,29⟩, ⟨1599,13,41⟩,
  ⟨1605,5,5⟩, ⟨1611,179,179⟩, ⟨1615,5,17⟩, ⟨1617,7,11⟩, ⟨1625,5,5⟩, ⟨1629,3,3⟩,
  ⟨1635,3,5⟩, ⟨1645,5,5⟩, ⟨1647,3,61⟩, ⟨1653,3,29⟩, ⟨1659,3,7⟩, ⟨1665,3,5⟩,
  ⟨1675,67,67⟩, ⟨1677,13,43⟩, ⟨1683,11,17⟩, ⟨1695,3,5⟩, ⟨1701,3,7⟩, ⟨1705,5,31⟩]

set_option maxRecDepth 30000 in
private theorem rows_1561_valid : ∀ z : Fin rows_1561.length, (rows_1561.get z).exactValid := exactValid_of_all (by decide +kernel)

set_option maxRecDepth 30000 in
private theorem covers_1561_1711 : Covers 1561 1711 :=
  covers_of_table rows_1561 rows_1561_valid (by decide +kernel)

private def rows_1711 : List Row := [
  ⟨1715,5,5⟩, ⟨1719,191,191⟩, ⟨1725,5,5⟩, ⟨1729,13,19⟩, ⟨1737,3,3⟩, ⟨1743,3,7⟩,
  ⟨1749,11,11⟩, ⟨1755,5,5⟩, ⟨1767,3,19⟩, ⟨1771,7,11⟩, ⟨1773,197,197⟩, ⟨1775,5,5⟩,
  ⟨1791,3,3⟩, ⟨1805,19,19⟩, ⟨1809,3,67⟩, ⟨1813,7,37⟩, ⟨1815,3,5⟩, ⟨1825,73,73⟩,
  ⟨1827,3,7⟩, ⟨1833,47,47⟩, ⟨1845,3,5⟩, ⟨1855,5,5⟩, ⟨1859,11,11⟩]

set_option maxRecDepth 30000 in
private theorem rows_1711_valid : ∀ z : Fin rows_1711.length, (rows_1711.get z).exactValid := exactValid_of_all (by decide +kernel)

set_option maxRecDepth 30000 in
private theorem covers_1711_1861 : Covers 1711 1861 :=
  covers_of_table rows_1711 rows_1711_valid (by decide +kernel)

private def rows_1861 : List Row := [
  ⟨1863,3,3⟩, ⟨1869,3,89⟩, ⟨1875,3,3⟩, ⟨1881,3,11⟩, ⟨1885,5,5⟩, ⟨1887,3,17⟩,
  ⟨1899,3,3⟩, ⟨1905,3,5⟩, ⟨1911,7,13⟩, ⟨1917,3,71⟩, ⟨1925,5,7⟩, ⟨1935,3,5⟩,
  ⟨1947,11,11⟩, ⟨1953,3,7⟩, ⟨1955,5,5⟩, ⟨1965,3,5⟩, ⟨1971,3,73⟩, ⟨1975,5,5⟩,
  ⟨1989,13,17⟩, ⟨2001,3,23⟩, ⟨2007,3,3⟩, ⟨2009,41,41⟩]

set_option maxRecDepth 30000 in
private theorem rows_1861_valid : ∀ z : Fin rows_1861.length, (rows_1861.get z).exactValid := exactValid_of_all (by decide +kernel)

set_option maxRecDepth 30000 in
private theorem covers_1861_2011 : Covers 1861 2011 :=
  covers_of_table rows_1861 rows_1861_valid (by decide +kernel)

private def rows_2011 : List Row := [
  ⟨2013,11,11⟩, ⟨2015,5,31⟩, ⟨2023,7,17⟩, ⟨2035,5,11⟩, ⟨2037,3,7⟩, ⟨2043,227,227⟩,
  ⟨2055,3,5⟩, ⟨2057,17,17⟩, ⟨2061,3,3⟩, ⟨2065,5,7⟩, ⟨2067,3,53⟩, ⟨2075,83,83⟩,
  ⟨2079,7,11⟩, ⟨2085,3,5⟩, ⟨2091,3,17⟩, ⟨2093,7,23⟩, ⟨2097,233,233⟩, ⟨2107,7,43⟩,
  ⟨2109,3,19⟩, ⟨2115,5,5⟩, ⟨2121,3,101⟩, ⟨2125,5,5⟩, ⟨2133,3,79⟩, ⟨2135,5,5⟩,
  ⟨2139,3,23⟩, ⟨2145,5,11⟩, ⟨2151,3,3⟩]

set_option maxRecDepth 30000 in
private theorem rows_2011_valid : ∀ z : Fin rows_2011.length, (rows_2011.get z).exactValid := exactValid_of_all (by decide +kernel)

set_option maxRecDepth 30000 in
private theorem covers_2011_2161 : Covers 2011 2161 :=
  covers_of_table rows_2011 rows_2011_valid (by decide +kernel)

private def rows_2161 : List Row := [
  ⟨2163,3,7⟩, ⟨2169,3,3⟩, ⟨2175,3,5⟩, ⟨2185,5,19⟩, ⟨2187,3,3⟩, ⟨2193,3,17⟩,
  ⟨2197,13,13⟩, ⟨2211,11,11⟩, ⟨2223,13,19⟩, ⟨2225,89,89⟩, ⟨2233,11,11⟩, ⟨2235,3,149⟩,
  ⟨2241,3,83⟩, ⟨2247,7,107⟩, ⟨2255,5,5⟩, ⟨2259,251,251⟩, ⟨2261,7,17⟩, ⟨2265,3,5⟩,
  ⟨2275,5,5⟩, ⟨2277,3,11⟩, ⟨2289,3,7⟩, ⟨2295,5,5⟩, ⟨2299,19,19⟩, ⟨2301,13,59⟩,
  ⟨2303,47,47⟩]

set_option maxRecDepth 30000 in
private theorem rows_2161_valid : ∀ z : Fin rows_2161.length, (rows_2161.get z).exactValid := exactValid_of_all (by decide +kernel)

set_option maxRecDepth 30000 in
private theorem covers_2161_2311 : Covers 2161 2311 :=
  covers_of_table rows_2161 rows_2161_valid (by decide +kernel)

private def rows_2311 : List Row := [
  ⟨2313,257,257⟩, ⟨2325,3,31⟩, ⟨2331,3,7⟩, ⟨2337,3,41⟩, ⟨2343,11,11⟩, ⟨2345,5,5⟩,
  ⟨2349,29,29⟩, ⟨2355,3,5⟩, ⟨2365,5,43⟩, ⟨2367,3,3⟩, ⟨2373,3,7⟩, ⟨2375,5,19⟩]

set_option maxRecDepth 30000 in
private theorem rows_2311_valid : ∀ z : Fin rows_2311.length, (rows_2311.get z).exactValid := exactValid_of_all (by decide +kernel)

set_option maxRecDepth 30000 in
private theorem covers_2311_2379 : Covers 2311 2379 :=
  covers_of_table rows_2311 rows_2311_valid (by decide +kernel)

theorem covers_343_2379 : Covers 343 2379 := by
  apply covers_append covers_343_511
  apply covers_append covers_511_661
  apply covers_append covers_661_811
  apply covers_append covers_811_961
  apply covers_append covers_961_1111
  apply covers_append covers_1111_1261
  apply covers_append covers_1261_1411
  apply covers_append covers_1411_1561
  apply covers_append covers_1561_1711
  apply covers_append covers_1711_1861
  apply covers_append covers_1861_2011
  apply covers_append covers_2011_2161
  apply covers_append covers_2161_2311
  exact covers_2311_2379

end OddPerfect.IndexSieve
