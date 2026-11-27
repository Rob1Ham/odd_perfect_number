module

public import OddPerfect.HarmonicTau5.Part020
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_600 : Closed 5 ⟨539415333601,540045491701,4,1⟩ := by
  exact closed_size (c:=540045491701) [(4524851,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_4524851) (by decide +kernel)

theorem htauRoot5_857 : RootAt 5 857 := by
  intro e he hdiv
  have cases := allowed_list (p:=857) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_600

theorem htau5_602 : Closed 5 ⟨544468370161,545102948681,4,1⟩ := by
  exact closed_size (c:=545102948681) [(4772771,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_4772771) (by decide +kernel)

theorem htauRoot5_859 : RootAt 5 859 := by
  intro e he hdiv
  have cases := allowed_list (p:=859) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_602

theorem htau5_604 : Closed 5 ⟨554680863361,555324344641,4,1⟩ := by
  exact closed_size (c:=555324344641) [(827607071,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_827607071) (by decide +kernel)

theorem htauRoot5_863 : RootAt 5 863 := by
  intro e he hdiv
  have cases := allowed_list (p:=863) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_604

theorem htau5_606 : Closed 5 ⟨591559418641,592234714781,4,1⟩ := by
  exact closed_size (c:=592234714781) [(203447171,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_203447171) (by decide +kernel)

theorem htauRoot5_877 : RootAt 5 877 := by
  intro e he hdiv
  have cases := allowed_list (p:=877) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_606

theorem htau5_608 : Closed 5 ⟨495941698630381961,496505871852933810,5,2⟩ := by
  exact closed_size (c:=16550195728431127) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_609 : Closed 5 ⟨408279539922174275955601,408743990450684193151015,6,2⟩ := by
  exact closed_size (c:=81748798090136838630203) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_610 : Closed 5 ⟨602425897921,603110472805,4,1⟩ := by
  apply closed_split (c:=120622094561) (p:=823241) (by decide +kernel) (by decide +kernel) htauPrime5_823241 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=823241) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_608
  · exact htau5_609

theorem htauRoot5_881 : RootAt 5 881 := by
  intro e he hdiv
  have cases := allowed_list (p:=881) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_610

theorem htau5_612 : Closed 5 ⟨607914936721,608604182681,4,1⟩ := by
  exact closed_size (c:=608604182681) [(184511,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_184511) (by decide +kernel)

theorem htauRoot5_883 : RootAt 5 883 := by
  intro e he hdiv
  have cases := allowed_list (p:=883) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_612

theorem htau5_614 : Closed 5 ⟨619005459361,619704111121,4,1⟩ := by
  exact closed_size (c:=619704111121) [(6011,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_6011) (by decide +kernel)

theorem htauRoot5_887 : RootAt 5 887 := by
  intro e he hdiv
  have cases := allowed_list (p:=887) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_614

theorem htau5_616 : Closed 5 ⟨676751377201,677498343401,4,1⟩ := by
  exact closed_size (c:=677498343401) [(31,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact (by norm_num)) (by decide +kernel)

theorem htauRoot5_907 : RootAt 5 907 := by
  intro e he hdiv
  have cases := allowed_list (p:=907) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_616

theorem htau5_618 : Closed 5 ⟨688768866241,689525755105,4,1⟩ := by
  exact closed_size (c:=137905151021) [(17884211,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_17884211) (by decide +kernel)

theorem htauRoot5_911 : RootAt 5 911 := by
  intro e he hdiv
  have cases := allowed_list (p:=911) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_618

theorem htau5_620 : Closed 5 ⟨509327260408601717309681,509882083133071646496882,5,2⟩ := by
  exact closed_size (c:=84980347188845274416147) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_621 : Closed 5 ⟨713283282721,714060279761,4,1⟩ := by
  apply closed_split (c:=714060279761) (p:=714060279761) (by decide +kernel) (by decide +kernel) htauPrime5_714060279761 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=714060279761) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_620

theorem htauRoot5_919 : RootAt 5 919 := by
  intro e he hdiv
  have cases := allowed_list (p:=919) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_621

theorem htau5_623 : Closed 5 ⟨744839767681,745642396741,4,1⟩ := by
  exact closed_size (c:=745642396741) [(316991,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_316991) (by decide +kernel)

theorem htauRoot5_929 : RootAt 5 929 := by
  intro e he hdiv
  have cases := allowed_list (p:=929) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_623

theorem htau5_625 : Closed 5 ⟨770829564961,771653100821,4,1⟩ := by
  exact closed_size (c:=771653100821) [(91525691,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_91525691) (by decide +kernel)

theorem htauRoot5_937 : RootAt 5 937 := by
  intro e he hdiv
  have cases := allowed_list (p:=937) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_625

theorem htau5_627 : Closed 5 ⟨123086026789469904055241,123216969371945573208210,5,2⟩ := by
  exact closed_size (c:=4107232312398185773607) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_628 : Closed 5 ⟨784076601361,784910725405,4,1⟩ := by
  apply closed_split (c:=156982145081) (p:=156982145081) (by decide +kernel) (by decide +kernel) htauPrime5_156982145081 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=156982145081) (r:=1) (E:=2) [1] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_627

theorem htauRoot5_941 : RootAt 5 941 := by
  intro e he hdiv
  have cases := allowed_list (p:=941) (r:=5) (E:=6) [4] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_628

end OddPerfect.HarmonicChain
