module

public import OddPerfect.HarmonicTau5.Part002
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_60 : Closed 5 ⟨82366061580625,104415112233399,8,3⟩ := by
  apply closed_split (c:=34805037411133) (p:=8715961) (by decide +kernel) (by decide +kernel) htauPrime5_8715961 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=8715961) (r:=1) (E:=3) [1, 2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_58
  · exact htau5_59

theorem htau5_61 : Closed 5 ⟨421137672861735625,533874468853362340,9,3⟩ := by
  exact closed_size (c:=26693723442668117) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_62 : Closed 5 ⟨2153276921342054250625,2729700159247245637673,10,3⟩ := by
  exact closed_size (c:=2729700159247245637673) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_63 : Closed 5 ⟨3150625,3993253,6,2⟩ := by
  apply closed_split (c:=3993253) (p:=5113) (by decide +kernel) (by decide +kernel) htauPrime5_5113 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=5113) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_57
  · exact htau5_60
  · exact htau5_61
  · exact htau5_62

theorem htau5_64 : Closed 5 ⟨707095906125625,900477285315465,10,3⟩ := by
  exact closed_size (c:=60031819021031) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_65 : Closed 5 ⟨31480616836618950625,40090153487099273525,12,3⟩ := by
  exact closed_size (c:=1603606139483970941) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_66 : Closed 5 ⟨1401548542183112300775625,1784853723403414326062785,14,3⟩ := by
  exact closed_size (c:=356970744680682865212557) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_67 : Closed 5 ⟨15882300625,20130044605,8,2⟩ := by
  apply closed_split (c:=4026008921) (p:=211) (by decide +kernel) (by decide +kernel) htauPrime5_211 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=211) (r:=1) (E:=7) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_64
  · exact htau5_65
  · exact htau5_66

theorem htau5_68 : Closed 5 ⟨80062677450625,101475554910037,10,2⟩ := by
  exact closed_size (c:=101475554910037) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_69 : Closed 5 ⟨403595957028600625,511538272301552749,12,2⟩ := by
  exact closed_size (c:=511538272301552749) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_70 : Closed 5 ⟨625,781,4,1⟩ := by
  apply closed_split (c:=781) (p:=71) (by decide +kernel) (by decide +kernel) htauPrime5_71 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=71) (r:=1) (E:=9) [2, 4, 6, 8] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_63
  · exact htau5_67
  · exact htau5_68
  · exact htau5_69

theorem htau5_71 : Closed 5 ⟨128722141759765625,163296570573351336,13,4⟩ := by
  exact closed_size (c:=6804023773889639) [(1279,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_1279) (by decide +kernel)

theorem htau5_72 : Closed 5 ⟨329142516479720703125,417549394793655368244,14,4⟩ := by
  exact closed_size (c:=11598594299823760229) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_73 : Closed 5 ⟨841617414638645837890625,1067673802551214372602000,15,4⟩ := by
  exact closed_size (c:=177945633758535728767) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_74 : Closed 5 ⟨2152015729231017407486328125,2730041913123518988339316092,16,4⟩ := by
  exact closed_size (c:=227503492760293249028276341) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_75 : Closed 5 ⟨50341080078125,63837596002092,12,3⟩ := by
  apply closed_split (c:=5319799666841) (p:=2557) (by decide +kernel) (by decide +kernel) htauPrime5_2557 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=2557) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_71
  · exact htau5_72
  · exact htau5_73
  · exact htau5_74

theorem htau5_76 : Closed 5 ⟨257393942439453125,326401640841605274,13,3⟩ := by
  exact closed_size (c:=18133424491200293) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_77 : Closed 5 ⟨1316055227692923828125,1668891589635610674840,14,3⟩ := by
  exact closed_size (c:=13907429913630088957) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_78 : Closed 5 ⟨6728990379193919533203125,8533042697806889863365798,15,3⟩ := by
  exact closed_size (c:=1422173782967814977227633) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_79 : Closed 5 ⟨9845703125,12482908878,11,2⟩ := by
  apply closed_split (c:=2080484813) (p:=5113) (by decide +kernel) (by decide +kernel) htauPrime5_5113 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=5113) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_75
  · exact htau5_76
  · exact htau5_77
  · exact htau5_78

theorem htau5_80 : Closed 5 ⟨49632189453125,62926519435230,13,2⟩ := by
  exact closed_size (c:=2097550647841) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_81 : Closed 5 ⟨250195867033203125,317212584648775662,15,2⟩ := by
  exact closed_size (c:=52868764108129277) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_82 : Closed 5 ⟨1261237365714376953125,1599068639214653893374,17,2⟩ := by
  exact closed_size (c:=266511439869108982229) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_83 : Closed 5 ⟨1953125,2441406,9,1⟩ := by
  apply closed_split (c:=406901) (p:=71) (by decide +kernel) (by decide +kernel) htauPrime5_71 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=71) (r:=1) (E:=9) [2, 4, 6, 8] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_79
  · exact htau5_80
  · exact htau5_81
  · exact htau5_82

theorem htau5_84 : Closed 5 ⟨6103515625,7629394531,14,1⟩ := by
  exact closed_size (c:=7629394531) [(71,1),(31,1),(11,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl
    · exact htauPrime5_71
    · exact (by norm_num)
    · exact (by norm_num)) (by decide +kernel)

theorem htau5_85 : Closed 5 ⟨19073486328125,23841857910156,19,1⟩ := by
  exact closed_size (c:=1986821492513) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot5_5 : RootAt 5 5 := by
  intro e he hdiv
  have cases := allowed_list (p:=5) (r:=5) (E:=22) [4, 9, 14, 19] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_70
  · exact htau5_83
  · exact htau5_84
  · exact htau5_85

theorem htau5_87 : Closed 5 ⟨194071279700702839001,226989598476099123882,9,4⟩ := by
  exact closed_size (c:=12610533248672173549) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_88 : Closed 5 ⟨1466692360889,1715323195914,7,3⟩ := by
  apply closed_split (c:=285887199319) (p:=11503) (by decide +kernel) (by decide +kernel) htauPrime5_11503 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=11503) (r:=1) (E:=4) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_87

theorem htau5_89 : Closed 5 ⟨319869470293921121,374093124146740482,9,3⟩ := by
  exact closed_size (c:=62348854024456747) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

end OddPerfect.HarmonicChain
