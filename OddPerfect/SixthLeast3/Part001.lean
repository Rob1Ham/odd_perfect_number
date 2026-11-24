module

public import OddPerfect.SixthLeast3.Primes
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase3_0 : Closed 3 ⟨85810206861322673732380411891963407843917051068145415840129742100493,166491887643063836106070598806102613175383765544929267062711842081750,23,8⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_1 : Closed 3 ⟨79951137945197103059985988442618401937876978005829848357533,154266884218339710021917202454266304213601984345845353610350,19,7⟩ := by
  apply closed_split (p:=181) sixPrime3_181 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_0
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_2 : Closed 3 ⟨2545049690601743626173547404435175790833181034093,4899046021604485567640201261844233087883878079270,15,6⟩ := by
  apply closed_split (p:=421) sixPrime3_421 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_1
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_3 : Closed 3 ⟨538398730893933,1036380609896814,11,5⟩ := by
  apply closed_split (p:=262209281) sixPrime3_262209281 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_2
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_4 : Closed 3 ⟨2069613,3952494,7,4⟩ := by
  apply closed_split (p:=127) sixPrime3_127 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_3
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_5 : Closed 3 ⟨24312571057624848669418293,46790662678773687318987342,15,6⟩ := by
  apply closed_split (p:=11) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_6 : Closed 3 ⟨17035317810693,32755258004742,11,5⟩ := by
  apply closed_split (p:=1093) sixPrime3_1093 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_5
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_7 : Closed 3 ⟨388422281401611093,746852854678910070,13,5⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_8 : Closed 3 ⟨747130293,1427057814,9,4⟩ := by
  apply closed_split (p:=151) sixPrime3_151 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_6
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_7
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_9 : Closed 3 ⟨5733,10374,5,3⟩ := by
  apply closed_split (p:=19) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_4
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_8
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_10 : Closed 3 ⟨55012776669964527273289312016598918200531609544664288981008412677,106936191189493135794743125797243446158664713130398891636248471150,29,10⟩ := by
  apply closed_split (p:=11) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_11 : Closed 3 ⟨92900725133825496552634344822593594391015994977237,180547800527554186607074339188499658435249100234150,25,9⟩ := by
  apply closed_split (p:=4933) sixPrime3_4933 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_10
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_12 : Closed 3 ⟨17822197272227807744142066946019312757,34613604552950937198497031869616196230,21,8⟩ := by
  apply closed_split (p:=1511) sixPrime3_1511 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_11
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_13 : Closed 3 ⟨112420059172017151815468117,217992012576995397657730086,17,7⟩ := by
  apply closed_split (p:=631) sixPrime3_631 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_12
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_14 : Closed 3 ⟨5578848897389735877,10656399741137541846,13,6⟩ := by
  apply closed_split (p:=67) sixPrime3_67 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_13
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_15 : Closed 3 ⟨1548294061623683695916074682197389194516066414973,2957501245245897223223805834915337132189144123110,19,7⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
