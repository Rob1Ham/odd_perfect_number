module

public import OddPerfect.HarmonicTau5.Part004
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_120 : Closed 5 ⟨32238474974381,35109865524006,7,3⟩ := by
  apply closed_split (c:=216727564963) (p:=31) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=31) (r:=1) (E:=11) [2, 4, 6, 8, 10] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · exact htau5_115
  · exact htau5_116
  · exact htau5_117
  · exact htau5_118
  · exact htau5_119

theorem htau5_121 : Closed 5 ⟨1176091805540393261,1280843187997535910,9,3⟩ := by
  exact closed_size (c:=1581287886416711) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_122 : Closed 5 ⟨42905005157919086554541,46726440341521923805734,11,3⟩ := by
  exact closed_size (c:=288434816922974838307) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_123 : Closed 5 ⟨883705901,957376422,5,2⟩ := by
  apply closed_split (c:=5909731) (p:=191) (by decide +kernel) (by decide +kernel) htauPrime5_191 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=191) (r:=1) (E:=7) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_120
  · exact htau5_121
  · exact htau5_122

theorem htau5_124 : Closed 5 ⟨27342744282841,29622183904043,6,2⟩ := by
  exact closed_size (c:=29622183904043) [(14083,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_14083) (by decide +kernel)

theorem htau5_125 : Closed 5 ⟨846011850855383381,916539992175025404,7,2⟩ := by
  exact closed_size (c:=2828827136342671) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_126 : Closed 5 ⟨28561,30941,4,1⟩ := by
  apply closed_split (c:=30941) (p:=30941) (by decide +kernel) (by decide +kernel) htauPrime5_30941 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=30941) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_123
  · exact htau5_124
  · exact htau5_125

theorem htau5_127 : Closed 5 ⟨10604499373,11488207654,9,1⟩ := by
  exact closed_size (c:=5744103827) [(2411,1),(11,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl
    · exact htauPrime5_2411
    · exact (by norm_num)) (by decide +kernel)

theorem htauRoot5_13 : RootAt 5 13 := by
  intro e he hdiv
  have cases := allowed_list (p:=13) (r:=5) (E:=14) [4, 9] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_126
  · exact htau5_127

theorem htau5_129 : Closed 5 ⟨14592121500564341101,15504642318743959686,7,3⟩ := by
  exact closed_size (c:=2584107053123993281) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_130 : Closed 5 ⟨7411737061,7875053822,5,2⟩ := by
  apply closed_split (c:=3937526911) (p:=44371) (by decide +kernel) (by decide +kernel) htauPrime5_44371 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=44371) (r:=1) (E:=4) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_129

theorem htau5_131 : Closed 5 ⟨657724958530201,698840151306843,6,2⟩ := by
  exact closed_size (c:=232946717102281) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_132 : Closed 5 ⟨58367170544928566941,62015773867120643404,7,2⟩ := by
  exact closed_size (c:=15503943466780160851) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_133 : Closed 5 ⟨83521,88741,4,1⟩ := by
  apply closed_split (c:=88741) (p:=88741) (by decide +kernel) (by decide +kernel) htauPrime5_88741 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=88741) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_130
  · exact htau5_131
  · exact htau5_132

theorem htau5_134 : Closed 5 ⟨10523606748220277,11181458169597276,10,2⟩ := by
  exact closed_size (c:=310596060266591) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_135 : Closed 5 ⟨933875386443815601257,992253779554231488294,11,2⟩ := by
  exact closed_size (c:=18375069991745027561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_136 : Closed 5 ⟨82873035668410640271147437,88053592651422182502316632,12,2⟩ := by
  exact closed_size (c:=1222966564603085868087731) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_137 : Closed 5 ⟨118587876497,125999618778,9,1⟩ := by
  apply closed_split (c:=6999978821) (p:=88741) (by decide +kernel) (by decide +kernel) htauPrime5_88741 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=88741) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_134
  · exact htau5_135
  · exact htau5_136

theorem htauRoot5_17 : RootAt 5 17 := by
  intro e he hdiv
  have cases := allowed_list (p:=17) (r:=5) (E:=13) [4, 9] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_133
  · exact htau5_137

theorem htau5_139 : Closed 5 ⟨89859685812185953,94956199241863042,7,3⟩ := by
  exact closed_size (c:=47478099620931521) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_140 : Closed 5 ⟨74658392342395891888849,78892743884829086992299,8,3⟩ := by
  exact closed_size (c:=26297581294943028997433) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_141 : Closed 5 ⟨108156134641,114290218313,6,2⟩ := by
  apply closed_split (c:=114290218313) (p:=830833) (by decide +kernel) (by decide +kernel) htauPrime5_830833 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=830833) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_139
  · exact htau5_140

theorem htau5_142 : Closed 5 ⟨89761047417393361,94851852397998905,8,2⟩ := by
  exact closed_size (c:=18970370479599781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_143 : Closed 5 ⟨130321,137561,4,1⟩ := by
  apply closed_split (c:=137561) (p:=911) (by decide +kernel) (by decide +kernel) htauPrime5_911 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=911) (r:=1) (E:=6) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_141
  · exact htau5_142

theorem htauRoot5_19 : RootAt 5 19 := by
  intro e he hdiv
  have cases := allowed_list (p:=19) (r:=5) (E:=12) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_143

theorem htau5_145 : Closed 5 ⟨4852844943674717401,5074104418121139882,7,3⟩ := by
  exact closed_size (c:=845684069686856647) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_146 : Closed 5 ⟨81870562801,85592231282,5,2⟩ := by
  apply closed_split (c:=42796115641) (p:=7699) (by decide +kernel) (by decide +kernel) htauPrime5_7699 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=7699) (r:=1) (E:=4) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_145

theorem htau5_147 : Closed 5 ⟨23952133723623361,25040948776385763,6,2⟩ := by
  exact closed_size (c:=8346982925461921) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_148 : Closed 5 ⟨279841,292561,4,1⟩ := by
  apply closed_split (c:=292561) (p:=292561) (by decide +kernel) (by decide +kernel) htauPrime5_292561 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=292561) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_146
  · exact htau5_147

theorem htauRoot5_23 : RootAt 5 23 := by
  intro e he hdiv
  have cases := allowed_list (p:=23) (r:=5) (E:=12) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_148

end OddPerfect.HarmonicChain
