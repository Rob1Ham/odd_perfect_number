module

public import OddPerfect.SixthLeast3.Part005
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase3_80 : Closed 3 ⟨160337228930131516913154200423142598883732527209,281290095192452385269022513063857292663776280675,22,7⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_81 : Closed 3 ⟨7138373769198385264490538157038731644902655843871889,12523317661161783978474602448299764687543886877362375,24,7⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_82 : Closed 3 ⟨3601384266528863163746416307431158304704129,6288200996858077599736715915853112750402975,20,6⟩ := by
  apply closed_split (p:=211) sixPrime3_211 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_80
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_81
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_83 : Closed 3 ⟨141721606946382774274020530457279009,243967913380893306043142527367553295,16,5⟩ := by
  apply closed_split (p:=71) sixPrime3_71 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_79
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_82
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_84 : Closed 3 ⟨9679776446033930351343523697649,15148582016820447441362466772279,12,4⟩ := by
  apply closed_split (p:=11) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_74
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_83
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_85 : Closed 3 ⟨246084698545569,385088390752559,8,3⟩ := by
  apply closed_split (p:=14083) sixPrime3_14083 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_73
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_84
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_86 : Closed 3 ⟨138156291096857885758679782177694429638449,237636287283628128178037936527604309035985,14,5⟩ := by
  apply closed_split (p:=7) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_87 : Closed 3 ⟨28506156965597578321566369,49032129879447420166005545,12,4⟩ := by
  apply closed_split (p:=69617111) sixPrime3_69617111 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_86
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_88 : Closed 3 ⟨16716911222719804176800253643501025986252329,28775431629344594017348127577271183436274725,16,5⟩ := by
  apply closed_split (p:=7) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_89 : Closed 3 ⟨81019214758189430617674072151782823480021626582187430391609,139461342103015542874390576059661401141009703907352493974125,18,5⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_90 : Closed 3 ⟨3449244992837306976909530649,5937311666981208284011423325,14,4⟩ := by
  apply closed_split (p:=69617111) sixPrime3_69617111 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_88
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_89
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_91 : Closed 3 ⟨235588074095847754723689,368662630672536993729365,10,3⟩ := by
  apply closed_split (p:=11) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_87
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_90
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_92 : Closed 3 ⟨257049,402233,6,2⟩ := by
  apply closed_split (p:=30941) sixPrime3_30941 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_85
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_91
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_93 : Closed 3 ⟨93324461719767081475805385740365425093,184695951252802304318479759749358742850,25,7⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_94 : Closed 3 ⟨153602004772700765443743437493,302053388167635482011147727850,21,6⟩ := by
  apply closed_split (p:=157) sixPrime3_157 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_93
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_95 : Closed 3 ⟨295453469911933116693,577152038891405274570,17,5⟩ := by
  apply closed_split (p:=151) sixPrime3_151 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_94
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
