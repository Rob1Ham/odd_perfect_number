module

public import OddPerfect.HarmonicTau5.Part003
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_90 : Closed 5 ⟨6725201,7848402,5,2⟩ := by
  apply closed_split (c:=1308067) (p:=467) (by decide +kernel) (by decide +kernel) htauPrime5_467 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=467) (r:=1) (E:=6) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_88
  · exact htau5_89

theorem htau5_91 : Closed 5 ⟨92924341708933,108465981146002,7,3⟩ := by
  exact closed_size (c:=54232990573001) [(2467,1),(43,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl
    · exact htauPrime5_2467
    · exact htauPrime5_43) (by decide +kernel)

theorem htau5_92 : Closed 5 ⟨458395777650166489,535062706976604669,8,3⟩ := by
  exact closed_size (c:=178354235658868223) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_93 : Closed 5 ⟨2261266371148271290237,2639464333537574208980,9,3⟩ := by
  exact closed_size (c:=131973216676878710449) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_94 : Closed 5 ⟨11154827008874422274739121,13020477557340875556275143,10,3⟩ := by
  exact closed_size (c:=13020477557340875556275143) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_95 : Closed 5 ⟨18837288001,21983376803,6,2⟩ := by
  apply closed_split (c:=21983376803) (p:=4933) (by decide +kernel) (by decide +kernel) htauPrime5_4933 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=4933) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_91
  · exact htau5_92
  · exact htau5_93
  · exact htau5_94

theorem htau5_96 : Closed 5 ⟨52763243690801,61575438428004,7,2⟩ := by
  exact closed_size (c:=5131286535667) [(467,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_467) (by decide +kernel)

theorem htau5_97 : Closed 5 ⟨147789845577933601,172472803036842005,8,2⟩ := by
  exact closed_size (c:=34494560607368401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_98 : Closed 5 ⟨2401,2801,4,1⟩ := by
  apply closed_split (c:=2801) (p:=2801) (by decide +kernel) (by decide +kernel) htauPrime5_2801 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=2801) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_90
  · exact htau5_95
  · exact htau5_96
  · exact htau5_97

theorem htau5_99 : Closed 5 ⟨678223072849,791260251657,14,1⟩ := by
  exact closed_size (c:=263753417219) [(159871,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_159871) (by decide +kernel)

theorem htauRoot5_7 : RootAt 5 7 := by
  intro e he hdiv
  have cases := allowed_list (p:=7) (r:=5) (E:=18) [4, 14] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_98
  · exact htau5_99

theorem htau5_101 : Closed 5 ⟨32014702997489061509,35432483249969442630,9,4⟩ := by
  exact closed_size (c:=131231419444331269) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_102 : Closed 5 ⟨678315009361926217029641981,750729601007099505544231710,11,4⟩ := by
  exact closed_size (c:=8341440011189994506047019) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_103 : Closed 5 ⟨1511010657101,1671957678510,7,3⟩ := by
  apply closed_split (c:=18577307539) (p:=4603) (by decide +kernel) (by decide +kernel) htauPrime5_4603 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=4603) (r:=1) (E:=5) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_101
  · exact htau5_102

theorem htau5_104 : Closed 5 ⟨48414292464173141,53571205317394710,9,3⟩ := by
  exact closed_size (c:=595235614637719) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_105 : Closed 5 ⟨1551242344844571610781,1716474989583984158910,11,3⟩ := by
  exact closed_size (c:=19071944328710935099) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_106 : Closed 5 ⟨47158661,51890310,5,2⟩ := by
  apply closed_split (c:=576559) (p:=179) (by decide +kernel) (by decide +kernel) htauPrime5_179 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=179) (r:=1) (E:=7) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_103
  · exact htau5_104
  · exact htau5_105

theorem htau5_107 : Closed 5 ⟨151898047081,167138704615,6,2⟩ := by
  exact closed_size (c:=33427740923) [(10378063,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_10378063) (by decide +kernel)

theorem htau5_108 : Closed 5 ⟨489263609647901,538353767581020,7,2⟩ := by
  exact closed_size (c:=2990854264339) [(179,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_179) (by decide +kernel)

theorem htau5_109 : Closed 5 ⟨1575918086675889121,1734037485378481525,8,2⟩ := by
  exact closed_size (c:=69361499415139261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_110 : Closed 5 ⟨14641,16105,4,1⟩ := by
  apply closed_split (c:=3221) (p:=3221) (by decide +kernel) (by decide +kernel) htauPrime5_3221 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=3221) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_106
  · exact htau5_107
  · exact htau5_108
  · exact htau5_109

theorem htau5_111 : Closed 5 ⟨379749833583241,417724816941565,14,1⟩ := by
  exact closed_size (c:=83544963388313) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_11 : RootAt 5 11 := by
  intro e he hdiv
  have cases := allowed_list (p:=11) (r:=5) (E:=15) [4, 14] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_110
  · exact htau5_111

theorem htau5_113 : Closed 5 ⟨3394328453958098628101,3831320152865384218494,11,5⟩ := by
  exact closed_size (c:=2627791600044845143) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_114 : Closed 5 ⟨371886019744103243793373661,419763278842964386854623190,13,5⟩ := by
  exact closed_size (c:=172742090058833081010133) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_115 : Closed 5 ⟨30981174450380141,34864096465337958,9,4⟩ := by
  apply closed_split (c:=71736824002753) (p:=331) (by decide +kernel) (by decide +kernel) htauPrime5_331 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=331) (r:=1) (E:=6) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_113
  · exact htau5_114

theorem htau5_116 : Closed 5 ⟨29772908646815315501,33505520218886545830,11,4⟩ := by
  exact closed_size (c:=41364839776403143) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_117 : Closed 5 ⟨28611765209589518196461,32198806053865667310822,13,4⟩ := by
  exact closed_size (c:=198758062060899180931) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_118 : Closed 5 ⟨27495906366415526986799021,30943052618888421982468134,15,4⟩ := by
  exact closed_size (c:=21222944183051043883723) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_119 : Closed 5 ⟨26423566018125321434313859181,29736273566752897040848644966,17,4⟩ := by
  exact closed_size (c:=183557244239215413832399043) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

end OddPerfect.HarmonicChain
