module

public import OddPerfect.HarmonicTau5.Part029
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_870 : Closed 5 ⟨10197605570161,10203315315721,4,1⟩ := by
  exact closed_size (c:=10203315315721) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1787 : RootAt 5 1787 := by
  intro e he hdiv
  have cases := allowed_list (p:=1787) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_870

theorem htau5_872 : Closed 5 ⟨10243334671441,10249063605821,4,1⟩ := by
  exact closed_size (c:=10249063605821) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1789 : RootAt 5 1789 := by
  intro e he hdiv
  have cases := allowed_list (p:=1789) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_872

theorem htau5_874 : Closed 5 ⟨10520947447201,10526792418005,4,1⟩ := by
  exact closed_size (c:=2105358483601) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1801 : RootAt 5 1801 := by
  intro e he hdiv
  have cases := allowed_list (p:=1801) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_874

theorem htau5_876 : Closed 5 ⟨10756569837841,10762512694105,4,1⟩ := by
  exact closed_size (c:=2152502538821) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1811 : RootAt 5 1811 := by
  intro e he hdiv
  have cases := allowed_list (p:=1811) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_876

theorem htau5_878 : Closed 5 ⟨11044515642241,11050577396161,4,1⟩ := by
  exact closed_size (c:=11050577396161) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1823 : RootAt 5 1823 := by
  intro e he hdiv
  have cases := allowed_list (p:=1823) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_878

theorem htau5_880 : Closed 5 ⟨11239665258721,11245807152305,4,1⟩ := by
  exact closed_size (c:=2249161430461) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1831 : RootAt 5 1831 := by
  intro e he hdiv
  have cases := allowed_list (p:=1831) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_880

theorem htau5_882 : Closed 5 ⟨11637711365281,11644015650961,4,1⟩ := by
  exact closed_size (c:=11644015650961) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1847 : RootAt 5 1847 := by
  intro e he hdiv
  have cases := allowed_list (p:=1847) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_882

theorem htau5_884 : Closed 5 ⟨11994592349041,12001041054605,4,1⟩ := by
  exact closed_size (c:=2400208210921) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1861 : RootAt 5 1861 := by
  intro e he hdiv
  have cases := allowed_list (p:=1861) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_884

theorem htau5_886 : Closed 5 ⟨12150027804721,12156539073641,4,1⟩ := by
  exact closed_size (c:=12156539073641) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1867 : RootAt 5 1867 := by
  intro e he hdiv
  have cases := allowed_list (p:=1867) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_886

theorem htau5_888 : Closed 5 ⟨12254487410881,12261040612705,4,1⟩ := by
  exact closed_size (c:=2452208122541) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1871 : RootAt 5 1871 := by
  intro e he hdiv
  have cases := allowed_list (p:=1871) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_888

theorem htau5_890 : Closed 5 ⟨12306969080641,12313543316261,4,1⟩ := by
  exact closed_size (c:=12313543316261) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1873 : RootAt 5 1873 := by
  intro e he hdiv
  have cases := allowed_list (p:=1873) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_890

theorem htau5_892 : Closed 5 ⟨12412437950641,12419054388781,4,1⟩ := by
  exact closed_size (c:=12419054388781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1877 : RootAt 5 1877 := by
  intro e he hdiv
  have cases := allowed_list (p:=1877) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_892

theorem htau5_894 : Closed 5 ⟨12465425870881,12472063477841,4,1⟩ := by
  exact closed_size (c:=12472063477841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1879 : RootAt 5 1879 := by
  intro e he hdiv
  have cases := allowed_list (p:=1879) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_894

theorem htau5_896 : Closed 5 ⟨12732914759041,12739658887621,4,1⟩ := by
  exact closed_size (c:=12739658887621) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1889 : RootAt 5 1889 := by
  intro e he hdiv
  have cases := allowed_list (p:=1889) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_896

theorem htau5_898 : Closed 5 ⟨13059557667601,13066431119005,4,1⟩ := by
  exact closed_size (c:=2613286223801) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1901 : RootAt 5 1901 := by
  intro e he hdiv
  have cases := allowed_list (p:=1901) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_898

end OddPerfect.HarmonicChain
