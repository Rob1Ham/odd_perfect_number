module

public import OddPerfect.SixthLeast5.Part005
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase5_80 : Closed 5 ⟨46128300625,64311339565,10,3⟩ := by
  apply closed_split (p:=3221) sixPrime5_3221 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact sixCase5_59
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_79
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_81 : Closed 5 ⟨21529231045398149578265239095785566731965416163438125,30675885600099970235516046657905128426863166340491250,23,7⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_82 : Closed 5 ⟨352938213858986058660085886816156831671564199400625,494772348388709197347033010611373039142954295814375,22,6⟩ := by
  apply closed_split (p:=61) sixPrime5_61 (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase5_81
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_83 : Closed 5 ⟨853749032341609965014365800625,1196833991561401079808073670375,18,5⟩ := by
  apply closed_split (p:=142591) sixPrime5_142591 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_82
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_84 : Closed 5 ⟨1581417261336043312005375074179500625,2216920736962383927192228264946300625,20,5⟩ := by
  apply closed_split (p:=58044391) sixPrime5_58044391 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_85 : Closed 5 ⟨460907711104938056100625,645651921909733800120125,16,4⟩ := by
  apply closed_split (p:=1361) sixPrime5_1361 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact sixCase5_83
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_84
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_86 : Closed 5 ⟨232532763450625,324194368363525,12,3⟩ := by
  apply closed_split (p:=211) sixPrime5_211 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_85
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_87 : Closed 5 ⟨9150625,12578005,8,2⟩ := by
  apply closed_split (p:=71) sixPrime5_71 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_80
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_86
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_88 : Closed 5 ⟨625,781,4,1⟩ := by
  apply closed_split (p:=11) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_38
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_87
  · exact closed_impossible (by decide +kernel)

theorem no_sixth_free_min_5 {N : ℕ} (H : Hyp N 5) (hd : 5∣N) : False := by
  apply root_split H (by norm_num) hd
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact sixCase5_14
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_88
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

end OddPerfect.SixthPowerChain
