module

public import OddPerfect.HarmonicTau5.Part006
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_180 : Closed 5 ⟨3418801,3500201,4,1⟩ := by
  apply closed_split (c:=3500201) (p:=3500201) (by decide +kernel) (by decide +kernel) htauPrime5_3500201 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=3500201) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_178
  · exact htau5_179

theorem htauRoot5_43 : RootAt 5 43 := by
  intro e he hdiv
  have cases := allowed_list (p:=43) (r:=5) (E:=10) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_180

theorem htau5_182 : Closed 5 ⟨167088832970058257,176490439846357428,8,4⟩ := by
  exact closed_size (c:=4902512217954373) [(331,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_331) (by decide +kernel)

theorem htau5_183 : Closed 5 ⟨160572368484225984977,169613000198970921780,10,4⟩ := by
  exact closed_size (c:=2826883336649515363) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_184 : Closed 5 ⟨154310046113341171562897,162998098878717677264052,12,4⟩ := by
  exact closed_size (c:=13583174906559806438671) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_185 : Closed 5 ⟨148291954314920865871944017,156641173028135194472187444,14,4⟩ := by
  exact closed_size (c:=1450381231741992541409143) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_186 : Closed 5 ⟨142508568096638952102938200337,150532167280043609394393567156,16,4⟩ := by
  exact closed_size (c:=12544347273336967449532797263) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_187 : Closed 5 ⟨173869753350737,177734581919796,6,3⟩ := by
  apply closed_split (c:=14811215159983) (p:=31) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=31) (r:=1) (E:=11) [2, 4, 6, 8, 10] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · exact htau5_182
  · exact htau5_183
  · exact htau5_184
  · exact htau5_185
  · exact htau5_186

theorem htau5_188 : Closed 5 ⟨423720588915746069,433139249040340194,7,3⟩ := by
  exact closed_size (c:=24063291613352233) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_189 : Closed 5 ⟨1032607075187673170153,1055560349984210850120,8,3⟩ := by
  exact closed_size (c:=8796336249868423751) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_190 : Closed 5 ⟨2516463442232359515662861,2572400572911594743539782,9,3⟩ := by
  exact closed_size (c:=428733428818599123923297) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_191 : Closed 5 ⟨71345815901,72901797342,5,2⟩ := by
  apply closed_split (c:=12150299557) (p:=2437) (by decide +kernel) (by decide +kernel) htauPrime5_2437 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=2437) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_187
  · exact htau5_188
  · exact htau5_189
  · exact htau5_190

theorem htau5_192 : Closed 5 ⟨1043147174288521,1065897183923143,6,2⟩ := by
  exact closed_size (c:=1065897183923143) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_193 : Closed 5 ⟨15251854835272465541,15584482726145259564,7,2⟩ := by
  exact closed_size (c:=1298706893845438297) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_194 : Closed 5 ⟨4879681,4985761,4,1⟩ := by
  apply closed_split (c:=4985761) (p:=14621) (by decide +kernel) (by decide +kernel) htauPrime5_14621 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=14621) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_191
  · exact htau5_192
  · exact htau5_193

theorem htauRoot5_47 : RootAt 5 47 := by
  intro e he hdiv
  have cases := allowed_list (p:=47) (r:=5) (E:=9) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_194

theorem htau5_196 : Closed 5 ⟨2341619959018213,2405147965360382,7,3⟩ := by
  exact closed_size (c:=1202573982680191) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_197 : Closed 5 ⟨40493633951301957409,41592223904051213679,8,3⟩ := by
  exact closed_size (c:=13864074634683737893) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_198 : Closed 5 ⟨700256411919864749473837,719254327972896712278700,9,3⟩ := by
  exact closed_size (c:=7192543279728967122787) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_199 : Closed 5 ⟨135408544441,139074127753,6,2⟩ := by
  apply closed_split (c:=139074127753) (p:=17293) (by decide +kernel) (by decide +kernel) htauPrime5_17293 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=17293) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_196
  · exact htau5_197
  · exact htau5_198

theorem htau5_200 : Closed 5 ⟨2323746031152001,2386652167942405,8,2⟩ := by
  exact closed_size (c:=477330433588481) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_201 : Closed 5 ⟨39877805640599489161,40957337855121185377,10,2⟩ := by
  exact closed_size (c:=40957337855121185377) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_202 : Closed 5 ⟨7890481,8042221,4,1⟩ := by
  apply closed_split (c:=8042221) (p:=131) (by decide +kernel) (by decide +kernel) htauPrime5_131 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=131) (r:=1) (E:=8) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_199
  · exact htau5_200
  · exact htau5_201

theorem htauRoot5_53 : RootAt 5 53 := by
  intro e he hdiv
  have cases := allowed_list (p:=53) (r:=5) (E:=9) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_202

theorem htau5_204 : Closed 5 ⟨301982727339973,309520089805542,7,3⟩ := by
  exact closed_size (c:=51586681634257) [(547,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_547) (by decide +kernel)

theorem htau5_205 : Closed 5 ⟨330067120982590489,338305741082585199,8,3⟩ := by
  exact closed_size (c:=37589526786953911) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_206 : Closed 5 ⟨360763363233971404477,369768175286190750300,9,3⟩ := by
  exact closed_size (c:=1232560584287302501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_207 : Closed 5 ⟨394314356014730745093361,404156615588089415205693,10,3⟩ := by
  exact closed_size (c:=134718871862696471735231) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_208 : Closed 5 ⟨276287948161,282925127793,6,2⟩ := by
  apply closed_split (c:=94308375931) (p:=1093) (by decide +kernel) (by decide +kernel) htauPrime5_1093 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=1093) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_204
  · exact htau5_205
  · exact htau5_206
  · exact htau5_207

theorem htau5_209 : Closed 5 ⟨6299641506018961,6450977712402905,8,2⟩ := by
  exact closed_size (c:=1290195542480581) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

end OddPerfect.HarmonicChain
