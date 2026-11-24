module

public import OddPerfect.SixthLeast3.Part006
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase3_96 : Closed 3 ⟨21338788298373,41000798054034,13,4⟩ := by
  apply closed_split (p:=61) sixPrime3_61 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_95
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_97 : Closed 3 ⟨163740213,298055394,9,3⟩ := by
  apply closed_split (p:=19) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_96
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_98 : Closed 3 ⟨1483007758509325492682087046374909277,2892143791864769820098528120619336030,25,7⟩ := by
  apply closed_split (p:=11) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_99 : Closed 3 ⟨2440870920686519043294812877,4729837473291618982463199030,21,6⟩ := by
  apply closed_split (p:=157) sixPrime3_157 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_98
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_100 : Closed 3 ⟨2643005324931992930637,4956316348852430808246,17,5⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_99
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_101 : Closed 3 ⟨29854589296077,55407885946686,13,4⟩ := by
  apply closed_split (p:=97) sixPrime3_97 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_100
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_102 : Closed 3 ⟨111088926770702517,206173651693510410,15,4⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_103 : Closed 3 ⟨8023270437,14646546642,11,3⟩ := by
  apply closed_split (p:=61) sixPrime3_61 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_101
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_102
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_104 : Closed 3 ⟨3341637,5229042,7,2⟩ := by
  apply closed_split (p:=7) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_97
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_103
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_105 : Closed 3 ⟨9,13,2,1⟩ := by
  apply closed_split (p:=13) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase3_22
  · exact sixCase3_58
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_92
  · exact sixCase3_104

theorem sixCase3_106 : Closed 3 ⟨480249,917301,8,3⟩ := by
  apply closed_split (p:=19) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_107 : Closed 3 ⟨23532201,45076493,10,3⟩ := by
  apply closed_split (p:=19) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_108 : Closed 3 ⟨9801,16093,6,2⟩ := by
  apply closed_split (p:=7) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_106
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_107
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_109 : Closed 3 ⟨3918253214802390133439862128149245,7738630280438452116159206851308270,15,6⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_110 : Closed 3 ⟨284109748801261499683458298415661530685104341725920137612657845,562161682185054229956428412555153151424528116890756440961407130,21,8⟩ := by
  apply closed_split (p:=7) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_111 : Closed 3 ⟨678171771249660132650518519665347777476875045,1341883496626487742549290755760853254026230510,19,7⟩ := by
  apply closed_split (p:=647251721) sixPrime3_647251721 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_110
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
