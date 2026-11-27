module

public import OddPerfect.HarmonicTau5.Part059
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1770 : Closed 5 ⟨917060634094081,917227311781121,4,1⟩ := by
  exact closed_size (c:=917227311781121) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5503 : RootAt 5 5503 := by
  intro e he hdiv
  have cases := allowed_list (p:=5503) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1770

theorem htau5_1772 : Closed 5 ⟨919729901048401,919896942439801,4,1⟩ := by
  exact closed_size (c:=919896942439801) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5507 : RootAt 5 5507 := by
  intro e he hdiv
  have cases := allowed_list (p:=5507) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1772

theorem htau5_1774 : Closed 5 ⟨927772672528321,927940808206561,4,1⟩ := by
  exact closed_size (c:=927940808206561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5519 : RootAt 5 5519 := by
  intro e he hdiv
  have cases := allowed_list (p:=5519) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1774

theorem htau5_1776 : Closed 5 ⟨929118245436481,929286563959205,4,1⟩ := by
  exact closed_size (c:=185857312791841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5521 : RootAt 5 5521 := by
  intro e he hdiv
  have cases := allowed_list (p:=5521) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1776

theorem htau5_1778 : Closed 5 ⟨933163747057441,933332614908881,4,1⟩ := by
  exact closed_size (c:=933332614908881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5527 : RootAt 5 5527 := by
  intro e he hdiv
  have cases := allowed_list (p:=5527) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1778

theorem htau5_1780 : Closed 5 ⟨935868077825521,936037312559305,4,1⟩ := by
  exact closed_size (c:=187207462511861) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5531 : RootAt 5 5531 := by
  intro e he hdiv
  have cases := allowed_list (p:=5531) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1780

theorem htau5_1782 : Closed 5 ⟨953589778302001,953761410731501,4,1⟩ := by
  exact closed_size (c:=953761410731501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5557 : RootAt 5 5557 := by
  intro e he hdiv
  have cases := allowed_list (p:=5557) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1782

theorem htau5_1784 : Closed 5 ⟨957714890286961,957887079228041,4,1⟩ := by
  exact closed_size (c:=957887079228041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5563 : RootAt 5 5563 := by
  intro e he hdiv
  have cases := allowed_list (p:=5563) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1784

theorem htau5_1786 : Closed 5 ⟨961853371365121,962026118019461,4,1⟩ := by
  exact closed_size (c:=962026118019461) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5569 : RootAt 5 5569 := by
  intro e he hdiv
  have cases := allowed_list (p:=5569) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1786

theorem htau5_1788 : Closed 5 ⟨964619800272241,964792919403661,4,1⟩ := by
  exact closed_size (c:=964792919403661) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5573 : RootAt 5 5573 := by
  intro e he hdiv
  have cases := allowed_list (p:=5573) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1788

theorem htau5_1790 : Closed 5 ⟨970170556248721,970344421939805,4,1⟩ := by
  exact closed_size (c:=194068884387961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5581 : RootAt 5 5581 := by
  intro e he hdiv
  have cases := allowed_list (p:=5581) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1790

theorem htau5_1792 : Closed 5 ⟨977142648636961,977317450541905,4,1⟩ := by
  exact closed_size (c:=195463490108381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5591 : RootAt 5 5591 := by
  intro e he hdiv
  have cases := allowed_list (p:=5591) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1792

theorem htau5_1794 : Closed 5 ⟨999706081460641,999883901823761,4,1⟩ := by
  exact closed_size (c:=999883901823761) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5623 : RootAt 5 5623 := by
  intro e he hdiv
  have cases := allowed_list (p:=5623) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1794

theorem htauRange5_3 : RootRange 5 3 83 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=3) [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] [0, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 0, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_3
  · exact htauRoot5_5
  · exact htauRoot5_7
  · exact htauRoot5_11
  · exact htauRoot5_13
  · exact htauRoot5_17
  · exact htauRoot5_19
  · exact htauRoot5_23
  · exact htauRoot5_29
  · exact htauRoot5_31
  · exact htauRoot5_37
  · exact htauRoot5_41
  · exact htauRoot5_43
  · exact htauRoot5_47
  · exact htauRoot5_53
  · exact htauRoot5_59
  · exact htauRoot5_61
  · exact htauRoot5_67
  · exact htauRoot5_71
  · exact htauRoot5_73
  · exact htauRoot5_79

theorem htauRange5_83 : RootRange 5 83 163 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=83) [83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157] [0, 2, 5, 2, 3, 2, 0, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 0, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_83
  · exact htauRoot5_89
  · exact htauRoot5_97
  · exact htauRoot5_101
  · exact htauRoot5_103
  · exact htauRoot5_107
  · exact htauRoot5_109
  · exact htauRoot5_113
  · exact htauRoot5_127
  · exact htauRoot5_131
  · exact htauRoot5_137
  · exact htauRoot5_139
  · exact htauRoot5_149
  · exact htauRoot5_151
  · exact htauRoot5_157

theorem htauRange5_163 : RootRange 5 163 243 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=163) [163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241] [0, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_163
  · exact htauRoot5_167
  · exact htauRoot5_173
  · exact htauRoot5_179
  · exact htauRoot5_181
  · exact htauRoot5_191
  · exact htauRoot5_193
  · exact htauRoot5_197
  · exact htauRoot5_199
  · exact htauRoot5_211
  · exact htauRoot5_223
  · exact htauRoot5_227
  · exact htauRoot5_229
  · exact htauRoot5_233
  · exact htauRoot5_239
  · exact htauRoot5_241

theorem htauRange5_243 : RootRange 5 243 323 := by
  intro p hlo hhi hp
  have pm := prime_mem_of_witnesses (a:=243) [251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317] [3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 7, 2, 17, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 0, 2, 3, 2, 0, 2, 0, 2, 3, 2, 0, 2, 11, 2, 3, 2] (by decide +kernel) hp hlo hhi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at pm
  rcases pm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htauRoot5_251
  · exact htauRoot5_257
  · exact htauRoot5_263
  · exact htauRoot5_269
  · exact htauRoot5_271
  · exact htauRoot5_277
  · exact htauRoot5_281
  · exact htauRoot5_283
  · exact htauRoot5_293
  · exact htauRoot5_307
  · exact htauRoot5_311
  · exact htauRoot5_313
  · exact htauRoot5_317

end OddPerfect.HarmonicChain
