module

public import OddPerfect.SixthLeast5.Primes
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase5_0 : Closed 5 ⟨3888708406545331756510377277226187698330810435519818596428781741025,6967970740886524085611107345605127692953470486188383567921911456025,34,11⟩ := by
  apply closed_split (p:=1291) sixPrime5_1291 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_1 : Closed 5 ⟨3045596192409549713100242623490528846117449450160097025,5452108782980454576242856789473945703277752561554530025,30,10⟩ := by
  apply closed_split (p:=1063) sixPrime5_1063 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_0
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_2 : Closed 5 ⟨10116337301659659398415262033511461651161267025,18108832940724999021231982994836317844762365425,28,9⟩ := by
  apply closed_split (p:=17351) sixPrime5_17351 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_1
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_3 : Closed 5 ⟨2959030754249709005705585681503972197025,5173655153154061444251910960209518780425,24,8⟩ := by
  apply closed_split (p:=43) sixPrime5_43 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_2
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_4 : Closed 5 ⟨377157945484317773196162496857025,659198457718603573778246473863475,22,7⟩ := by
  apply closed_split (p:=2801) sixPrime5_2801 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact sixCase5_3
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_5 : Closed 5 ⟨454450418153436017640429025,793418722798208031912847075,20,6⟩ := by
  apply closed_split (p:=911) sixPrime5_911 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_4
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_6 : Closed 5 ⟨874135419944889025,1516034090316044915,16,5⟩ := by
  apply closed_split (p:=151) sixPrime5_151 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_5
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_7 : Closed 5 ⟨6707556111025,11020813241515,12,4⟩ := by
  apply closed_split (p:=19) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_6
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_8 : Closed 5 ⟨2793651025,3934599515,8,3⟩ := by
  apply closed_split (p:=7) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_7
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_9 : Closed 5 ⟨1348096719743895821930949420342023859025,1902574979622679138405757836072189192225,18,6⟩ := by
  apply closed_split (p:=1291) sixPrime5_1291 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_10 : Closed 5 ⟨1055815403834638478829735025,1488675274684049812130138225,14,5⟩ := by
  apply closed_split (p:=1063) sixPrime5_1063 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_9
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_11 : Closed 5 ⟨3507025908457305025,4944540346736144825,12,4⟩ := by
  apply closed_split (p:=17351) sixPrime5_17351 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_10
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_12 : Closed 5 ⟨338031774025,476441542775,10,3⟩ := by
  apply closed_split (p:=3221) sixPrime5_3221 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact sixCase5_11
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_13 : Closed 5 ⟨23088025,29583455,6,2⟩ := by
  apply closed_split (p:=11) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_8
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_12
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_14 : Closed 5 ⟨25,31,2,1⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_13
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_15 : Closed 5 ⟨30246798837193946211797439156059075933405755319023735093298125,55015428732919162301024078061973187329832822020868485760687290,33,11⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
