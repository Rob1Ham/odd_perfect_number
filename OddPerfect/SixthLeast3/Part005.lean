module

public import OddPerfect.SixthLeast3.Part004
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase3_64 : Closed 3 ⟨1636486608419833413045165260510658962670753701637,2631702645317560251785201655499298966460920767098,21,8⟩ := by
  apply closed_split (p:=433) sixPrime3_433 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_63
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_65 : Closed 3 ⟨42014973176046371072891100290925170673477,66710771524432000235065476732592965422778,17,7⟩ := by
  apply closed_split (p:=79) sixPrime3_79 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_64
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_66 : Closed 3 ⟨150158466081560515791970299290555202612254017444470681,246376759836009027399808904304852100313787262038645255,24,8⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_67 : Closed 3 ⟨162593450589169619090383758778149281513093927961,258174021760348135449158187691411131990073678791,20,7⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_66
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_68 : Closed 3 ⟨267611294114945038680835033700160322761,422220072939443039462439726155651679891,16,6⟩ := by
  apply closed_split (p:=157) sixPrime3_157 (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase3_65
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_67
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_69 : Closed 3 ⟨1028701929381451446777391173321,1610240763901271059365895313811,12,5⟩ := by
  apply closed_split (p:=127) sixPrime3_127 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_68
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_70 : Closed 3 ⟨2623550995328616008121617803047776844321,4513953108814080495210734875662026207055,16,6⟩ := by
  apply closed_split (p:=7) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_71 : Closed 3 ⟨317449670434762536982715754168780998162841,546595600131208769739615677988999489207675,18,6⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_72 : Closed 3 ⟨21682239630815008331583618207006420201,33939497058752484926396502824526512835,14,5⟩ := by
  apply closed_split (p:=11) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_70
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_71
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_73 : Closed 3 ⟨48806197031839706780841,76380346466429764535907,10,4⟩ := by
  apply closed_split (p:=4591) sixPrime3_4591 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_69
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_72
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_74 : Closed 3 ⟨1171252949970105572512566367415529,2014761408237119509701208080713107,14,5⟩ := by
  apply closed_split (p:=7) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_75 : Closed 3 ⟨1812482452349107098868632086620194802757163630527805894468915215769,3164678157804644929106523091106046827440497105564979351239680493505,20,7⟩ := by
  apply closed_split (p:=7) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_76 : Closed 3 ⟨4418941410549097163669268668504482363954127241126304634755514999770076801174701819266155407469409,7972597575967600686835530440280699450221141072810354441070096552557953963217736699242922564733275,24,8⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_77 : Closed 3 ⟨4246602695537682374286167190432807551759916278722378754000049914779043805928888448314775346578102049,7661923192078309338822337237474393644353762368064738464134338862627208717893758530484408074660410875,26,8⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_78 : Closed 3 ⟨4598274100467322750956575097299149182054242706687101597040078043465220396643810425875291787169,8028799170158711668515136395046021601431159187120195811752363094217476297298828498734060991675,22,7⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_76
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_77
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_79 : Closed 3 ⟨714418620616715565115337494035143484369,1247407941116507473798587742430299997335,18,6⟩ := by
  apply closed_split (p:=50368674550301) sixPrime3_50368674550301 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_75
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_78
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
