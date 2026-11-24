module

public import OddPerfect.SixthLeast3.Part002
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase3_32 : Closed 3 ⟨10341391887428961177,19388814828110813358,13,6⟩ := by
  apply closed_split (p:=37) sixPrime3_37 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_31
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_33 : Closed 3 ⟨1891109649173685849390049484104759378159914898458271490263516008940951841319177,3545596154899363956841127746807756460272487926000920647462548170550198055123250,23,8⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_34 : Closed 3 ⟨127331918999018249284675024080925895258797777804704297,238731441416196053757286731635253468350618567730781650,19,7⟩ := by
  apply closed_split (p:=1963111) sixPrime3_1963111 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_33
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_35 : Closed 3 ⟨81134434533404545239232377,152116905011163129054492930,15,6⟩ := by
  apply closed_split (p:=6294091) sixPrime3_6294091 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_34
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_36 : Closed 3 ⟨1318113409977,2470415296986,11,5⟩ := by
  apply closed_split (p:=2801) sixPrime3_2801 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_32
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_35
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_37 : Closed 3 ⟨548985177,881976186,7,4⟩ := by
  apply closed_split (p:=7) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_36
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_38 : Closed 3 ⟨614032525206042559393116645327700955100681,1121474026779494934723463299716495382929625,22,7⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_39 : Closed 3 ⟨41939247674751899418968420553766884441,69635146027910272258519919262123277425,18,6⟩ := by
  apply closed_split (p:=11) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_38
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_40 : Closed 3 ⟨462724608314757154041,768255044960158025985,14,5⟩ := by
  apply closed_split (p:=17351) sixPrime3_17351 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_39
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_41 : Closed 3 ⟨501043948448121,805041412294977,10,4⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_40
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_42 : Closed 3 ⟨5659641,8999757,6,3⟩ := by
  apply closed_split (p:=97) sixPrime3_97 (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase3_37
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_41
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_43 : Closed 3 ⟨834592347092720690518005,1604897923187374408135530,13,6⟩ := by
  apply closed_split (p:=421) sixPrime3_421 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_44 : Closed 3 ⟨4172961735463603452590025,8291972603134767775366905,14,6⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_45 : Closed 3 ⟨166918469418544138103601,267482987197895734689255,12,5⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase3_43
  · exact sixCase3_44
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_46 : Closed 3 ⟨1927336964036326853975466376367025,3829756014051799937606152946153925,16,6⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_47 : Closed 3 ⟨77093478561453074159018655054681,123540516582316127019553320843675,14,5⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_46
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
