module

public import OddPerfect.HarmonicTau5.Part041
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1230 : Closed 5 ⟨108710671926481,108744349334141,4,1⟩ := by
  exact closed_size (c:=108744349334141) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3229 : RootAt 5 3229 := by
  intro e he hdiv
  have cases := allowed_list (p:=3229) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1230

theorem htau5_1232 : Closed 5 ⟨111703782138001,111738152532505,4,1⟩ := by
  exact closed_size (c:=22347630506501) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3251 : RootAt 5 3251 := by
  intro e he hdiv
  have cases := allowed_list (p:=3251) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1232

theorem htau5_1234 : Closed 5 ⟨111978914476081,112013348336621,4,1⟩ := by
  exact closed_size (c:=112013348336621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3253 : RootAt 5 3253 := by
  intro e he hdiv
  have cases := allowed_list (p:=3253) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1234

theorem htau5_1236 : Closed 5 ⟨112530703586401,112565264613301,4,1⟩ := by
  exact closed_size (c:=112565264613301) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3257 : RootAt 5 3257 := by
  intro e he hdiv
  have cases := allowed_list (p:=3257) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1236

theorem htau5_1238 : Closed 5 ⟨112807361608561,112841986335881,4,1⟩ := by
  exact closed_size (c:=112841986335881) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3259 : RootAt 5 3259 := by
  intro e he hdiv
  have cases := allowed_list (p:=3259) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1238

theorem htau5_1240 : Closed 5 ⟨114478037712481,114513046286705,4,1⟩ := by
  exact closed_size (c:=22902609257341) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3271 : RootAt 5 3271 := by
  intro e he hdiv
  have cases := allowed_list (p:=3271) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1240

theorem htau5_1242 : Closed 5 ⟨118448417326801,118484332553401,4,1⟩ := by
  exact closed_size (c:=118484332553401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3299 : RootAt 5 3299 := by
  intro e he hdiv
  have cases := allowed_list (p:=3299) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1242

theorem htau5_1244 : Closed 5 ⟨118735913353201,118771893933005,4,1⟩ := by
  exact closed_size (c:=23754378786601) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3301 : RootAt 5 3301 := by
  intro e he hdiv
  have cases := allowed_list (p:=3301) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1244

theorem htau5_1246 : Closed 5 ⟨119601542190001,119637719305001,4,1⟩ := by
  exact closed_size (c:=119637719305001) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3307 : RootAt 5 3307 := by
  intro e he hdiv
  have cases := allowed_list (p:=3307) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1246

theorem htau5_1248 : Closed 5 ⟨120471895488961,120508269853541,4,1⟩ := by
  exact closed_size (c:=120508269853541) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3313 : RootAt 5 3313 := by
  intro e he hdiv
  have cases := allowed_list (p:=3313) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1248

theorem htau5_1250 : Closed 5 ⟨121346990409121,121383562738961,4,1⟩ := by
  exact closed_size (c:=121383562738961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3319 : RootAt 5 3319 := by
  intro e he hdiv
  have cases := allowed_list (p:=3319) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1250

theorem htau5_1252 : Closed 5 ⟨121933029744241,121969734449161,4,1⟩ := by
  exact closed_size (c:=121969734449161) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3323 : RootAt 5 3323 := by
  intro e he hdiv
  have cases := allowed_list (p:=3323) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1252

theorem htau5_1254 : Closed 5 ⟨122816065582081,122852969447941,4,1⟩ := by
  exact closed_size (c:=122852969447941) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3329 : RootAt 5 3329 := by
  intro e he hdiv
  have cases := allowed_list (p:=3329) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1254

theorem htau5_1256 : Closed 5 ⟨123111473904721,123148444317305,4,1⟩ := by
  exact closed_size (c:=24629688863461) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3331 : RootAt 5 3331 := by
  intro e he hdiv
  have cases := allowed_list (p:=3331) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1256

theorem htau5_1258 : Closed 5 ⟨124895130571201,124932501944801,4,1⟩ := by
  exact closed_size (c:=124932501944801) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_3343 : RootAt 5 3343 := by
  intro e he hdiv
  have cases := allowed_list (p:=3343) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1258

end OddPerfect.HarmonicChain
