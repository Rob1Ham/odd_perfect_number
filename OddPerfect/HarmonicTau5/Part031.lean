module

public import OddPerfect.HarmonicTau5.Part030
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_900 : Closed 5 ⟨13225215949201,13232154677401,4,1⟩ := by
  exact closed_size (c:=13232154677401) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1907 : RootAt 5 1907 := by
  intro e he hdiv
  have cases := allowed_list (p:=1907) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_900

theorem htau5_902 : Closed 5 ⟨13392445265761,13399449682741,4,1⟩ := by
  exact closed_size (c:=13399449682741) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1913 : RootAt 5 1913 := by
  intro e he hdiv
  have cases := allowed_list (p:=1913) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_902

theorem htau5_904 : Closed 5 ⟨13903658595121,13910862563305,4,1⟩ := by
  exact closed_size (c:=2782172512661) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1931 : RootAt 5 1931 := by
  intro e he hdiv
  have cases := allowed_list (p:=1931) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_904

theorem htau5_906 : Closed 5 ⟨13961350047121,13968576418781,4,1⟩ := by
  exact closed_size (c:=13968576418781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1933 : RootAt 5 1933 := by
  intro e he hdiv
  have cases := allowed_list (p:=1933) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_906

theorem htau5_908 : Closed 5 ⟨14429369557201,14436776831101,4,1⟩ := by
  exact closed_size (c:=14436776831101) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1949 : RootAt 5 1949 := by
  intro e he hdiv
  have cases := allowed_list (p:=1949) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_908

theorem htau5_910 : Closed 5 ⟨14488688572801,14496118669505,4,1⟩ := by
  exact closed_size (c:=2899223733901) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1951 : RootAt 5 1951 := by
  intro e he hdiv
  have cases := allowed_list (p:=1951) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_910

theorem htau5_912 : Closed 5 ⟨15153339067441,15161023316461,4,1⟩ := by
  exact closed_size (c:=15161023316461) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1973 : RootAt 5 1973 := by
  intro e he hdiv
  have cases := allowed_list (p:=1973) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_912

theorem htau5_914 : Closed 5 ⟨15338510106481,15346264661641,4,1⟩ := by
  exact closed_size (c:=15346264661641) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1979 : RootAt 5 1979 := by
  intro e he hdiv
  have cases := allowed_list (p:=1979) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_914

theorem htau5_916 : Closed 5 ⟨15588038452561,15595887414521,4,1⟩ := by
  exact closed_size (c:=15595887414521) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1987 : RootAt 5 1987 := by
  intro e he hdiv
  have cases := allowed_list (p:=1987) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_916

theorem htau5_918 : Closed 5 ⟨15777173258401,15785093526101,4,1⟩ := by
  exact closed_size (c:=15785093526101) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1993 : RootAt 5 1993 := by
  intro e he hdiv
  have cases := allowed_list (p:=1993) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_918

theorem htau5_920 : Closed 5 ⟨15904215784081,15912183828061,4,1⟩ := by
  exact closed_size (c:=15912183828061) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1997 : RootAt 5 1997 := by
  intro e he hdiv
  have cases := allowed_list (p:=1997) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_920

theorem htau5_922 : Closed 5 ⟨15968023992001,15976015996001,4,1⟩ := by
  exact closed_size (c:=15976015996001) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1999 : RootAt 5 1999 := by
  intro e he hdiv
  have cases := allowed_list (p:=1999) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_922

theorem htau5_924 : Closed 5 ⟨16096216216081,16104256284121,4,1⟩ := by
  exact closed_size (c:=16104256284121) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2003 : RootAt 5 2003 := by
  intro e he hdiv
  have cases := allowed_list (p:=2003) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_924

theorem htau5_926 : Closed 5 ⟨16354914662641,16363051436105,4,1⟩ := by
  exact closed_size (c:=3272610287221) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2011 : RootAt 5 2011 := by
  intro e he hdiv
  have cases := allowed_list (p:=2011) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_926

theorem htau5_928 : Closed 5 ⟨16550975387521,16559185196741,4,1⟩ := by
  exact closed_size (c:=16559185196741) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_2017 : RootAt 5 2017 := by
  intro e he hdiv
  have cases := allowed_list (p:=2017) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_928

end OddPerfect.HarmonicChain
