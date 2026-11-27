module

public import OddPerfect.HarmonicTau5.Part055
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_1650 : Closed 5 ⟨618525306088561,618649358496521,4,1⟩ := by
  exact closed_size (c:=618649358496521) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4987 : RootAt 5 4987 := by
  intro e he hdiv
  have cases := allowed_list (p:=4987) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1650

theorem htau5_1652 : Closed 5 ⟨621507343142401,621631843812101,4,1⟩ := by
  exact closed_size (c:=621631843812101) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4993 : RootAt 5 4993 := by
  intro e he hdiv
  have cases := allowed_list (p:=4993) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1652

theorem htau5_1654 : Closed 5 ⟨624500149980001,624625099990001,4,1⟩ := by
  exact closed_size (c:=624625099990001) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_4999 : RootAt 5 4999 := by
  intro e he hdiv
  have cases := allowed_list (p:=4999) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1654

theorem htau5_1656 : Closed 5 ⟨626501350540081,626626600710121,4,1⟩ := by
  exact closed_size (c:=626626600710121) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5003 : RootAt 5 5003 := by
  intro e he hdiv
  have cases := allowed_list (p:=5003) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1656

theorem htau5_1658 : Closed 5 ⟨629512164586561,629637865897381,4,1⟩ := by
  exact closed_size (c:=629637865897381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5009 : RootAt 5 5009 := by
  intro e he hdiv
  have cases := allowed_list (p:=5009) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1658

theorem htau5_1660 : Closed 5 ⟨630518176634641,630644028566105,4,1⟩ := by
  exact closed_size (c:=126128805713221) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5011 : RootAt 5 5011 := by
  intro e he hdiv
  have cases := allowed_list (p:=5011) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1660

theorem htau5_1662 : Closed 5 ⟨635566335414481,635692942254205,4,1⟩ := by
  exact closed_size (c:=127138588450841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5021 : RootAt 5 5021 := by
  intro e he hdiv
  have cases := allowed_list (p:=5021) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1662

theorem htau5_1664 : Closed 5 ⟨636579593619841,636706351802561,4,1⟩ := by
  exact closed_size (c:=636706351802561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5023 : RootAt 5 5023 := by
  intro e he hdiv
  have cases := allowed_list (p:=5023) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1664

theorem htau5_1666 : Closed 5 ⟨644729338693441,644857311964321,4,1⟩ := by
  exact closed_size (c:=644857311964321) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5039 : RootAt 5 5039 := by
  intro e he hdiv
  have cases := allowed_list (p:=5039) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1666

theorem htau5_1668 : Closed 5 ⟨650892809785201,651021699450505,4,1⟩ := by
  exact closed_size (c:=130204339890101) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5051 : RootAt 5 5051 := by
  intro e he hdiv
  have cases := allowed_list (p:=5051) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1668

theorem htau5_1670 : Closed 5 ⟨655026269697361,655155772716281,4,1⟩ := by
  exact closed_size (c:=655155772716281) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5059 : RootAt 5 5059 := by
  intro e he hdiv
  have cases := allowed_list (p:=5059) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1670

theorem htau5_1672 : Closed 5 ⟨664398515813041,664529405985581,4,1⟩ := by
  exact closed_size (c:=664529405985581) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5077 : RootAt 5 5077 := by
  intro e he hdiv
  have cases := allowed_list (p:=5077) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1672

theorem htau5_1674 : Closed 5 ⟨666494821866721,666626021634805,4,1⟩ := by
  exact closed_size (c:=133325204326961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5081 : RootAt 5 5081 := by
  intro e he hdiv
  have cases := allowed_list (p:=5081) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1674

theorem htau5_1676 : Closed 5 ⟨669648577349761,669780242425921,4,1⟩ := by
  exact closed_size (c:=669780242425921) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5087 : RootAt 5 5087 := by
  intro e he hdiv
  have cases := allowed_list (p:=5087) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1676

theorem htau5_1678 : Closed 5 ⟨675989652039601,676122251029801,4,1⟩ := by
  exact closed_size (c:=676122251029801) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5099 : RootAt 5 5099 := by
  intro e he hdiv
  have cases := allowed_list (p:=5099) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_1678

end OddPerfect.HarmonicChain
