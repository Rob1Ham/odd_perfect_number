module

public import OddPerfect.SixthLeast3.Part001
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase3_16 : Closed 3 ⟨10315291611273621636573,19703930813697498735822,15,6⟩ := by
  apply closed_split (p:=3500201) sixPrime3_3500201 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_15
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_17 : Closed 3 ⟨3017224930984173,5629371231451422,11,5⟩ := by
  apply closed_split (p:=43) sixPrime3_43 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_14
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_16
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_18 : Closed 3 ⟨4130580930517332837,7706761252890966266,13,5⟩ := by
  apply closed_split (p:=11) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_19 : Closed 3 ⟨2203962696117,4000974578146,9,4⟩ := by
  apply closed_split (p:=37) sixPrime3_37 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_17
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_18
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_20 : Closed 3 ⟨17291411932618231317,31390050152705244910,11,4⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_21 : Closed 3 ⟨280917,509782,7,3⟩ := by
  apply closed_split (p:=2801) sixPrime3_2801 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_19
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_20
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_22 : Closed 3 ⟨117,182,3,2⟩ := by
  apply closed_split (p:=7) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_9
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_21
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_23 : Closed 3 ⟨35984751712800794422225799637219310322541337451846453901,59293052225821961495876257339831375950624963948241304250,19,7⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_24 : Closed 3 ⟨2199189908594079183367871566743639501,3623607935811417018349426176900140850,15,6⟩ := by
  apply closed_split (p:=63601) sixPrime3_63601 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_23
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_25 : Closed 3 ⟨1070272611384284061,1763442929180299770,11,5⟩ := by
  apply closed_split (p:=37861) sixPrime3_37861 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_24
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_26 : Closed 3 ⟨89162541,146465514,7,4⟩ := by
  apply closed_split (p:=331) sixPrime3_331 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_25
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_27 : Closed 3 ⟨85685201901,140758078890,9,4⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_28 : Closed 3 ⟨92781,147498,5,3⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_26
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_27
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_29 : Closed 3 ⟨39237757290420188722845904782485570241559549737,77425295257516477662420379209931541335243135758,25,9⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_30 : Closed 3 ⟨66261263756484260871469611191097,130722504780164227266652882283718,21,8⟩ := by
  apply closed_split (p:=4933) sixPrime3_4933 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_29
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_31 : Closed 3 ⟨19381433361135749308447497,37347142287018439017260118,17,7⟩ := by
  apply closed_split (p:=43) sixPrime3_43 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_30
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
