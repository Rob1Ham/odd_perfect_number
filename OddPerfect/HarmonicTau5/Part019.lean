module

public import OddPerfect.HarmonicTau5.Part018
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_540 : Closed 5 ⟨227988105361,228318522905,4,1⟩ := by
  exact closed_size (c:=45663704581) [(68053211,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_68053211) (by decide +kernel)

theorem htauRoot5_691 : RootAt 5 691 := by
  intro e he hdiv
  have cases := allowed_list (p:=691) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_540

theorem htau5_542 : Closed 5 ⟨115630590519159434101,115795777318863170510,5,2⟩ := by
  exact closed_size (c:=11579577731886317051) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_543 : Closed 5 ⟨241474942801,241819907005,4,1⟩ := by
  apply closed_split (c:=48363981401) (p:=478851301) (by decide +kernel) (by decide +kernel) htauPrime5_478851301 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=478851301) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_542

theorem htauRoot5_701 : RootAt 5 701 := by
  intro e he hdiv
  have cases := allowed_list (p:=701) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_543

theorem htau5_545 : Closed 5 ⟨252688187761,253045091981,4,1⟩ := by
  exact closed_size (c:=253045091981) [(103231,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_103231) (by decide +kernel)

theorem htauRoot5_709 : RootAt 5 709 := by
  intro e he hdiv
  have cases := allowed_list (p:=709) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_545

theorem htau5_547 : Closed 5 ⟨267248675521,267620888161,4,1⟩ := by
  exact closed_size (c:=267620888161) [(60671251,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_60671251) (by decide +kernel)

theorem htauRoot5_719 : RootAt 5 719 := by
  intro e he hdiv
  have cases := allowed_list (p:=719) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_547

theorem htau5_549 : Closed 5 ⟨5471601474038107241,5479138394914566762,5,2⟩ := by
  exact closed_size (c:=304396577495253709) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_550 : Closed 5 ⟨107174452184175495810470641,107322080875688259636239243,6,2⟩ := by
  exact closed_size (c:=107322080875688259636239243) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_551 : Closed 5 ⟨279342903841,279727673681,4,1⟩ := by
  apply closed_split (c:=279727673681) (p:=19587401) (by decide +kernel) (by decide +kernel) htauPrime5_19587401 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=19587401) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_549
  · exact htau5_550

theorem htauRoot5_727 : RootAt 5 727 := by
  intro e he hdiv
  have cases := allowed_list (p:=727) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_551

theorem htau5_553 : Closed 5 ⟨14793420119408847461,14813629998809679102,5,2⟩ := by
  exact closed_size (c:=2468938333134946517) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_554 : Closed 5 ⟨288679469521,289073840381,4,1⟩ := by
  apply closed_split (c:=289073840381) (p:=51245141) (by decide +kernel) (by decide +kernel) htauPrime5_51245141 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=51245141) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_553

theorem htauRoot5_733 : RootAt 5 733 := by
  intro e he hdiv
  have cases := allowed_list (p:=733) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_554

theorem htau5_556 : Closed 5 ⟨47862701817196640501,47927556725357096502,5,2⟩ := by
  exact closed_size (c:=7987926120892849417) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_557 : Closed 5 ⟨298248146641,298652276921,4,1⟩ := by
  apply closed_split (c:=298652276921) (p:=160479461) (by decide +kernel) (by decide +kernel) htauPrime5_160479461 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=160479461) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_556

theorem htauRoot5_739 : RootAt 5 739 := by
  intro e he hdiv
  have cases := allowed_list (p:=739) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_557

theorem htau5_559 : Closed 5 ⟨920818518533771971901,922059514146933720702,5,2⟩ := by
  exact closed_size (c:=5691725395968726671) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_560 : Closed 5 ⟨304758098401,305168823601,4,1⟩ := by
  apply closed_split (c:=305168823601) (p:=3021473501) (by decide +kernel) (by decide +kernel) htauPrime5_3021473501 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=3021473501) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_559

theorem htauRoot5_743 : RootAt 5 743 := by
  intro e he hdiv
  have cases := allowed_list (p:=743) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_560

theorem htau5_562 : Closed 5 ⟨318097128001,318521257505,4,1⟩ := by
  exact closed_size (c:=63704251501) [(125731,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_125731) (by decide +kernel)

theorem htauRoot5_751 : RootAt 5 751 := by
  intro e he hdiv
  have cases := allowed_list (p:=751) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_562

theorem htau5_564 : Closed 5 ⟨328385156401,328819528301,4,1⟩ := by
  exact closed_size (c:=328819528301) [(191,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_191) (by decide +kernel)

theorem htauRoot5_757 : RootAt 5 757 := by
  intro e he hdiv
  have cases := allowed_list (p:=757) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_564

theorem htau5_566 : Closed 5 ⟨22525700958978118878161,22555340039523034662810,5,2⟩ := by
  exact closed_size (c:=751844667984101155427) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_567 : Closed 5 ⟨335381132641,335822423605,4,1⟩ := by
  apply closed_split (c:=67164484721) (p:=67164484721) (by decide +kernel) (by decide +kernel) htauPrime5_67164484721 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=67164484721) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_566

theorem htauRoot5_761 : RootAt 5 761 := by
  intro e he hdiv
  have cases := allowed_list (p:=761) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_567

theorem htau5_569 : Closed 5 ⟨226348996316946674441,226643721922730037042,5,2⟩ := by
  exact closed_size (c:=1399035320510679241) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

end OddPerfect.HarmonicChain
