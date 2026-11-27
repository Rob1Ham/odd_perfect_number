module

public import OddPerfect.HarmonicTau7.Part006
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau7_180 : Closed 7 ⟨195930594145441,196746971621047,6,1⟩ := by
  exact closed_size (c:=196746971621047) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_241 : RootAt 7 241 := by
  intro e he hdiv
  have cases := allowed_list (p:=241) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_180

theorem htau7_182 : Closed 7 ⟨250058907189001,251059142817757,6,1⟩ := by
  exact closed_size (c:=251059142817757) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_251 : RootAt 7 251 := by
  intro e he hdiv
  have cases := allowed_list (p:=251) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_182

theorem htau7_184 : Closed 7 ⟨288136807515649,289262341920007,6,1⟩ := by
  exact closed_size (c:=289262341920007) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_257 : RootAt 7 257 := by
  intro e he hdiv
  have cases := allowed_list (p:=257) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_184

theorem htau7_186 : Closed 7 ⟨330928743953809,332191830762793,6,1⟩ := by
  exact closed_size (c:=332191830762793) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_263 : RootAt 7 263 := by
  intro e he hdiv
  have cases := allowed_list (p:=263) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_186

theorem htau7_188 : Closed 7 ⟨378890468381881,380304238786291,6,1⟩ := by
  exact closed_size (c:=380304238786291) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_269 : RootAt 7 269 := by
  intro e he hdiv
  have cases := allowed_list (p:=269) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_188

theorem htau7_190 : Closed 7 ⟨396109944105121,397577017972177,6,1⟩ := by
  exact closed_size (c:=397577017972177) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_271 : RootAt 7 271 := by
  intro e he hdiv
  have cases := allowed_list (p:=271) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_190

theorem htau7_192 : Closed 7 ⟨451729667968489,453366369664027,6,1⟩ := by
  exact closed_size (c:=453366369664027) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_277 : RootAt 7 277 := by
  intro e he hdiv
  have cases := allowed_list (p:=277) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_192

theorem htau7_194 : Closed 7 ⟨492309163417681,494067410429887,6,1⟩ := by
  exact closed_size (c:=70581058632841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_281 : RootAt 7 281 := by
  intro e he hdiv
  have cases := allowed_list (p:=281) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_194

theorem htau7_196 : Closed 7 ⟨513710701744969,515532370900093,6,1⟩ := by
  exact closed_size (c:=515532370900093) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_283 : RootAt 7 283 := by
  intro e he hdiv
  have cases := allowed_list (p:=283) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_196

theorem htau7_198 : Closed 7 ⟨632711491215049,634878311390443,6,1⟩ := by
  exact closed_size (c:=634878311390443) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_293 : RootAt 7 293 := by
  intro e he hdiv
  have cases := allowed_list (p:=293) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_198

theorem htau7_200 : Closed 7 ⟨837201991720249,839937945941557,6,1⟩ := by
  exact closed_size (c:=839937945941557) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_307 : RootAt 7 307 := by
  intro e he hdiv
  have cases := allowed_list (p:=307) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_200

theorem htau7_202 : Closed 7 ⟨904820297013361,907739072165017,6,1⟩ := by
  exact closed_size (c:=907739072165017) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_311 : RootAt 7 311 := by
  intro e he hdiv
  have cases := allowed_list (p:=311) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_202

theorem htau7_204 : Closed 7 ⟨940299110504209,943312889704543,6,1⟩ := by
  exact closed_size (c:=943312889704543) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_313 : RootAt 7 313 := by
  intro e he hdiv
  have cases := allowed_list (p:=313) (r:=7) (E:=7) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_204

theorem htauRange7_3 : RootRange 7 3 83 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3) [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] [0, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot7_3
  · exact htauRoot7_5
  · exact htauRoot7_7
  · exact htauRoot7_11
  · exact htauRoot7_13
  · exact htauRoot7_17
  · exact htauRoot7_19
  · exact htauRoot7_23
  · exact htauRoot7_29
  · exact htauRoot7_31
  · exact htauRoot7_37
  · exact htauRoot7_41
  · exact htauRoot7_43
  · exact htauRoot7_47
  · exact htauRoot7_53
  · exact htauRoot7_59
  · exact htauRoot7_61
  · exact htauRoot7_67
  · exact htauRoot7_71
  · exact htauRoot7_73
  · exact htauRoot7_79

theorem htauRange7_83 : RootRange 7 83 163 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=83) [83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157] [0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot7_83
  · exact htauRoot7_89
  · exact htauRoot7_97
  · exact htauRoot7_101
  · exact htauRoot7_103
  · exact htauRoot7_107
  · exact htauRoot7_109
  · exact htauRoot7_113
  · exact htauRoot7_127
  · exact htauRoot7_131
  · exact htauRoot7_137
  · exact htauRoot7_139
  · exact htauRoot7_149
  · exact htauRoot7_151
  · exact htauRoot7_157

theorem htauRange7_163 : RootRange 7 163 243 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=163) [163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241] [0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot7_163
  · exact htauRoot7_167
  · exact htauRoot7_173
  · exact htauRoot7_179
  · exact htauRoot7_181
  · exact htauRoot7_191
  · exact htauRoot7_193
  · exact htauRoot7_197
  · exact htauRoot7_199
  · exact htauRoot7_211
  · exact htauRoot7_223
  · exact htauRoot7_227
  · exact htauRoot7_229
  · exact htauRoot7_233
  · exact htauRoot7_239
  · exact htauRoot7_241

theorem htauRange7_243 : RootRange 7 243 317 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=243) [251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313] [3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot7_251
  · exact htauRoot7_257
  · exact htauRoot7_263
  · exact htauRoot7_269
  · exact htauRoot7_271
  · exact htauRoot7_277
  · exact htauRoot7_281
  · exact htauRoot7_283
  · exact htauRoot7_293
  · exact htauRoot7_307
  · exact htauRoot7_311
  · exact htauRoot7_313

end OddPerfect.HarmonicChain
