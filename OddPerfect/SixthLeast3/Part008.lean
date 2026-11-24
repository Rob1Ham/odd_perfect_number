module

public import OddPerfect.SixthLeast3.Part007
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase3_112 : Closed 3 ⟨2317102139358756231701130307964465672445,4576324151333584822982135629745460806370,17,6⟩ := by
  apply closed_split (p:=541) sixPrime3_541 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_111
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_113 : Closed 3 ⟨6625822830390218721626658045,13069118624828715463570066170,13,5⟩ := by
  apply closed_split (p:=769) sixPrime3_769 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_109
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_112
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_114 : Closed 3 ⟨492568032395011014367261487725443699373680682859466036480712221344745775846497766605,971596209797610920985467865307098507347263862030745798449506416866684224856667590430,21,8⟩ := by
  apply closed_split (p:=31810898376456201755581) sixPrime3_31810898376456201755581 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_115 : Closed 3 ⟨105253347477052561760157094348891750037958215664867508135903634263605,207613456937304365562949297203464505349199018858446363326493829463810,19,7⟩ := by
  apply closed_split (p:=68409301) sixPrime3_68409301 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_114
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_116 : Closed 3 ⟨784270160206402102699480841973626508256274893264605,1546982044673310345457918998448833139502906821495770,17,6⟩ := by
  apply closed_split (p:=366340651) sixPrime3_366340651 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_115
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_117 : Closed 3 ⟨713628891843823350024729544058044053040605,1407598856829487140788641733755097373840090,15,5⟩ := by
  apply closed_split (p:=33151) sixPrime3_33151 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_116
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_118 : Closed 3 ⟨61518709067805,121342699550490,11,4⟩ := by
  apply closed_split (p:=10378063) sixPrime3_10378063 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_113
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_117
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_119 : Closed 3 ⟨5929605,11692230,9,3⟩ := by
  apply closed_split (p:=3221) sixPrime3_3221 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_118
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_120 : Closed 3 ⟨1185921,1948705,8,2⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase3_119
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_121 : Closed 3 ⟨81,121,4,1⟩ := by
  apply closed_split (p:=11) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_108
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_120
  · exact closed_impossible (by decide +kernel)

theorem no_sixth_free_min_3 {N : ℕ} (H : Hyp N 3) (hd : 3∣N) : False := by
  apply root_split H (by norm_num) hd
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_105
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_121
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
