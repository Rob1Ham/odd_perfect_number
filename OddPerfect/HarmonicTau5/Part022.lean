module

public import OddPerfect.HarmonicTau5.Part021
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_630 : Closed 5 ⟨3577503767229582234661,3581285484490539315302,5,2⟩ := by
  exact closed_size (c:=1790642742245269657651) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_631 : Closed 5 ⟨804266382481,805116558361,4,1⟩ := by
  apply closed_split (c:=805116558361) (p:=4448157781) (by decide +kernel) (by decide +kernel) htauPrime5_4448157781 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=4448157781) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_630

theorem htauRoot5_947 : RootAt 5 947 := by
  intro e he hdiv
  have cases := allowed_list (p:=947) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_631

theorem htau5_633 : Closed 5 ⟨4801414523891101,4807283736562262,5,2⟩ := by
  exact closed_size (c:=2403641868281131) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_634 : Closed 5 ⟨27949033943570098921,27983199456238947123,6,2⟩ := by
  exact closed_size (c:=9327733152079649041) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_635 : Closed 5 ⟨162691326585521545819141,162890204035592621223004,7,2⟩ := by
  exact closed_size (c:=40722551008898155305751) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_636 : Closed 5 ⟨824843587681,825710020021,4,1⟩ := by
  apply closed_split (c:=825710020021) (p:=5821) (by decide +kernel) (by decide +kernel) htauPrime5_5821 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=5821) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_633
  · exact htau5_634
  · exact htau5_635

theorem htauRoot5_953 : RootAt 5 953 := by
  intro e he hdiv
  have cases := allowed_list (p:=953) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_636

theorem htau5_638 : Closed 5 ⟨765351857089169607159761,766144146797175643216722,5,2⟩ := by
  exact closed_size (c:=42563563710954202400929) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_639 : Closed 5 ⟨874391437921,875296605041,4,1⟩ := by
  apply closed_split (c:=875296605041) (p:=875296605041) (by decide +kernel) (by decide +kernel) htauPrime5_875296605041 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=875296605041) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_638

theorem htauRoot5_967 : RootAt 5 967 := by
  intro e he hdiv
  have cases := allowed_list (p:=967) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_639

theorem htau5_641 : Closed 5 ⟨888949151281,889865593705,4,1⟩ := by
  exact closed_size (c:=177973118741) [(620351,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_620351) (by decide +kernel)

theorem htauRoot5_971 : RootAt 5 971 := by
  intro e he hdiv
  have cases := allowed_list (p:=971) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_641

theorem htau5_643 : Closed 5 ⟨911125611841,912059142181,4,1⟩ := by
  exact closed_size (c:=912059142181) [(71,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_71) (by decide +kernel)

theorem htauRoot5_977 : RootAt 5 977 := by
  intro e he hdiv
  have cases := allowed_list (p:=977) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_643

theorem htau5_645 : Closed 5 ⟨933714431521,934665260881,4,1⟩ := by
  exact closed_size (c:=934665260881) [(84969569171,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_84969569171) (by decide +kernel)

theorem htauRoot5_983 : RootAt 5 983 := by
  intro e he hdiv
  have cases := allowed_list (p:=983) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_645

theorem htau5_647 : Closed 5 ⟨186233451169756420134541,186421565767862850509710,5,2⟩ := by
  exact closed_size (c:=18642156576786285050971) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_648 : Closed 5 ⟨964483090561,965457315905,4,1⟩ := by
  apply closed_split (c:=193091463181) (p:=193091463181) (by decide +kernel) (by decide +kernel) htauPrime5_193091463181 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=193091463181) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_647

theorem htauRoot5_991 : RootAt 5 991 := by
  intro e he hdiv
  have cases := allowed_list (p:=991) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_648

theorem htau5_650 : Closed 5 ⟨456436555270799296801,456894825893650770442,5,2⟩ := by
  exact closed_size (c:=228447412946825385221) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_651 : Closed 5 ⟨988053892081,989045914061,4,1⟩ := by
  apply closed_split (c:=989045914061) (p:=461955121) (by decide +kernel) (by decide +kernel) htauPrime5_461955121 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=461955121) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_650

theorem htauRoot5_997 : RootAt 5 997 := by
  intro e he hdiv
  have cases := allowed_list (p:=997) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_651

theorem htau5_653 : Closed 5 ⟨1036488922561,1037517185381,4,1⟩ := by
  exact closed_size (c:=1037517185381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1009 : RootAt 5 1009 := by
  intro e he hdiv
  have cases := allowed_list (p:=1009) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_653

theorem htau5_655 : Closed 5 ⟨1053022816561,1054063352941,4,1⟩ := by
  exact closed_size (c:=1054063352941) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1013 : RootAt 5 1013 := by
  intro e he hdiv
  have cases := allowed_list (p:=1013) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_655

theorem htau5_657 : Closed 5 ⟨1078193566321,1079252695561,4,1⟩ := by
  exact closed_size (c:=1079252695561) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_1019 : RootAt 5 1019 := by
  intro e he hdiv
  have cases := allowed_list (p:=1019) (r:=5) (E:=5) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_657

theorem htau5_659 : Closed 5 ⟨1086683238481,1087748614205,4,1⟩ := by
  exact closed_size (c:=217549722841) [(1451,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_1451) (by decide +kernel)

end OddPerfect.HarmonicChain
