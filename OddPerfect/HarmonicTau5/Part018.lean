module

public import OddPerfect.HarmonicTau5.Part017
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_510 : Closed 5 ⟨302618699456001168341,303118070383157693142,5,2⟩ := by
  exact closed_size (c:=50519678397192948857) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_511 : Closed 5 ⟨135754665601,135978683201,4,1⟩ := by
  apply closed_split (c:=135978683201) (p:=2229158741) (by decide +kernel) (by decide +kernel) htauPrime5_2229158741 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=2229158741) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_510

theorem htauRoot5_607 : RootAt 5 607 := by
  intro e he hdiv
  have cases := allowed_list (p:=607) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_511

theorem htau5_513 : Closed 5 ⟨141202341361,141433064141,4,1⟩ := by
  exact closed_size (c:=141433064141) [(53551,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_53551) (by decide +kernel)

theorem htauRoot5_613 : RootAt 5 613 := by
  intro e he hdiv
  have cases := allowed_list (p:=613) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_513

theorem htau5_515 : Closed 5 ⟨21037094805307647876661,21071245933383265843022,5,2⟩ := by
  exact closed_size (c:=10535622966691632921511) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_516 : Closed 5 ⟨144924114721,145159381141,4,1⟩ := by
  apply closed_split (c:=145159381141) (p:=145159381141) (by decide +kernel) (by decide +kernel) htauPrime5_145159381141 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=145159381141) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_515

theorem htauRoot5_617 : RootAt 5 617 := by
  intro e he hdiv
  have cases := allowed_list (p:=617) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_516

theorem htau5_518 : Closed 5 ⟨146812351921,147049912361,4,1⟩ := by
  exact closed_size (c:=147049912361) [(1031,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_1031) (by decide +kernel)

theorem htauRoot5_619 : RootAt 5 619 := by
  intro e he hdiv
  have cases := allowed_list (p:=619) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_518

theorem htau5_520 : Closed 5 ⟨158532181921,158783820305,4,1⟩ := by
  exact closed_size (c:=31756764061) [(1511,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_1511) (by decide +kernel)

theorem htauRoot5_631 : RootAt 5 631 := by
  intro e he hdiv
  have cases := allowed_list (p:=631) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_520

theorem htau5_522 : Closed 5 ⟨168823196161,169086982405,4,1⟩ := by
  exact closed_size (c:=33817396481) [(4091,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_4091) (by decide +kernel)

theorem htauRoot5_641 : RootAt 5 641 := by
  intro e he hdiv
  have cases := allowed_list (p:=641) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_522

theorem htau5_524 : Closed 5 ⟨170940075601,171206337401,4,1⟩ := by
  exact closed_size (c:=171206337401) [(3691,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_3691) (by decide +kernel)

theorem htauRoot5_643 : RootAt 5 643 := by
  intro e he hdiv
  have cases := allowed_list (p:=643) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_524

theorem htau5_526 : Closed 5 ⟨175233494881,175504754161,4,1⟩ := by
  exact closed_size (c:=175504754161) [(15954977651,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_15954977651) (by decide +kernel)

theorem htauRoot5_647 : RootAt 5 647 := by
  intro e he hdiv
  have cases := allowed_list (p:=647) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_526

theorem htau5_528 : Closed 5 ⟨181824635281,182103507421,4,1⟩ := by
  exact closed_size (c:=182103507421) [(31,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact (by norm_num)) (by decide +kernel)

theorem htauRoot5_653 : RootAt 5 653 := by
  intro e he hdiv
  have cases := allowed_list (p:=653) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_528

theorem htau5_530 : Closed 5 ⟨188599986961,188886613081,4,1⟩ := by
  exact closed_size (c:=188886613081) [(6131,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_6131) (by decide +kernel)

theorem htauRoot5_659 : RootAt 5 659 := by
  intro e he hdiv
  have cases := allowed_list (p:=659) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_530

theorem htau5_532 : Closed 5 ⟨190899960241,191189202605,4,1⟩ := by
  exact closed_size (c:=38237840521) [(230611,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_230611) (by decide +kernel)

theorem htauRoot5_661 : RootAt 5 661 := by
  intro e he hdiv
  have cases := allowed_list (p:=661) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_532

theorem htau5_534 : Closed 5 ⟨205144679041,205449953861,4,1⟩ := by
  exact closed_size (c:=205449953861) [(192811,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_192811) (by decide +kernel)

theorem htauRoot5_673 : RootAt 5 673 := by
  intro e he hdiv
  have cases := allowed_list (p:=673) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_534

theorem htau5_536 : Closed 5 ⟨210065472241,210376219981,4,1⟩ := by
  exact closed_size (c:=210376219981) [(193811,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_193811) (by decide +kernel)

theorem htauRoot5_677 : RootAt 5 677 := by
  intro e he hdiv
  have cases := allowed_list (p:=677) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_536

theorem htau5_538 : Closed 5 ⟨217611987121,217931066281,4,1⟩ := by
  exact closed_size (c:=217931066281) [(189340631,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_189340631) (by decide +kernel)

theorem htauRoot5_683 : RootAt 5 683 := by
  intro e he hdiv
  have cases := allowed_list (p:=683) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_538

end OddPerfect.HarmonicChain
