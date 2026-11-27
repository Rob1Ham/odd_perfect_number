module

public import OddPerfect.HarmonicTau7.Part005
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau7_150 : Closed 7 ⟨18755369578009,18871143464293,6,1⟩ := by
  exact closed_size (c:=18871143464293) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_163 : RootAt 7 163 := by
  intro e he hdiv
  have cases := allowed_list (p:=163) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_150

theorem htau7_152 : Closed 7 ⟨21691961596369,21822636063817,6,1⟩ := by
  exact closed_size (c:=21822636063817) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_167 : RootAt 7 167 := by
  intro e he hdiv
  have cases := allowed_list (p:=167) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_152

theorem htau7_154 : Closed 7 ⟨26808753332089,26964618177043,6,1⟩ := by
  exact closed_size (c:=26964618177043) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_173 : RootAt 7 173 := by
  intro e he hdiv
  have cases := allowed_list (p:=173) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_154

theorem htau7_156 : Closed 7 ⟨32894113444921,33078911835061,6,1⟩ := by
  exact closed_size (c:=33078911835061) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_179 : RootAt 7 179 := by
  intro e he hdiv
  have cases := allowed_list (p:=179) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_156

theorem htau7_158 : Closed 7 ⟨35161828327081,35357171817787,6,1⟩ := by
  exact closed_size (c:=35357171817787) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_181 : RootAt 7 181 := by
  intro e he hdiv
  have cases := allowed_list (p:=181) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_158

theorem htau7_160 : Closed 7 ⟨48551226272641,48806759042497,6,1⟩ := by
  exact closed_size (c:=48806759042497) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_191 : RootAt 7 191 := by
  intro e he hdiv
  have cases := allowed_list (p:=191) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_160

theorem htau7_162 : Closed 7 ⟨51682540549249,51951720447943,6,1⟩ := by
  exact closed_size (c:=51951720447943) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_193 : RootAt 7 193 := by
  intro e he hdiv
  have cases := allowed_list (p:=193) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_162

theorem htau7_164 : Closed 7 ⟨58451728309129,58749951412747,6,1⟩ := by
  exact closed_size (c:=8392850201821) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_197 : RootAt 7 197 := by
  intro e he hdiv
  have cases := allowed_list (p:=197) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_164

theorem htau7_166 : Closed 7 ⟨62103840598801,62417496359401,6,1⟩ := by
  exact closed_size (c:=62417496359401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_199 : RootAt 7 199 := by
  intro e he hdiv
  have cases := allowed_list (p:=199) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_166

theorem htau7_168 : Closed 7 ⟨88245939632761,88666158392917,6,1⟩ := by
  exact closed_size (c:=12666594056131) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_211 : RootAt 7 211 := by
  intro e he hdiv
  have cases := allowed_list (p:=211) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_168

theorem htau7_170 : Closed 7 ⟨122978496247489,123532453437793,6,1⟩ := by
  exact closed_size (c:=123532453437793) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_223 : RootAt 7 223 := by
  intro e he hdiv
  have cases := allowed_list (p:=223) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_170

theorem htau7_172 : Closed 7 ⟨136821750708889,137427156685477,6,1⟩ := by
  exact closed_size (c:=137427156685477) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_227 : RootAt 7 227 := by
  intro e he hdiv
  have cases := allowed_list (p:=227) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_172

theorem htau7_174 : Closed 7 ⟨144215816802121,144848342314411,6,1⟩ := by
  exact closed_size (c:=144848342314411) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_229 : RootAt 7 229 := by
  intro e he hdiv
  have cases := allowed_list (p:=229) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_174

theorem htau7_176 : Closed 7 ⟨160005726539569,160695406395343,6,1⟩ := by
  exact closed_size (c:=160695406395343) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_233 : RootAt 7 233 := by
  intro e he hdiv
  have cases := allowed_list (p:=233) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_176

theorem htau7_178 : Closed 7 ⟨186374892382561,187157980165681,6,1⟩ := by
  exact closed_size (c:=26736854309383) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_239 : RootAt 7 239 := by
  intro e he hdiv
  have cases := allowed_list (p:=239) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_178

end OddPerfect.HarmonicChain
