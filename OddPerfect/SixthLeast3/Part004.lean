module

public import OddPerfect.SixthLeast3.Part003
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase3_48 : Closed 3 ⟨361402494126921,579112191300435,10,4⟩ := by
  apply closed_split (p:=21491) sixPrime3_21491 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_45
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_47
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_49 : Closed 3 ⟨155050705042802282025,308082610796001279225,14,5⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_50 : Closed 3 ⟨6202028201712091281,9938148735354879975,12,4⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_49
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_51 : Closed 3 ⟨21059524161,33488243295,8,3⟩ := by
  apply closed_split (p:=131) sixPrime3_131 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_48
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_50
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_52 : Closed 3 ⟨1710050973794776041184660713714479727042428173013731103661,3318722648750011760710230600808484504895734759015418667350,29,8⟩ := by
  apply closed_split (p:=11) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_53 : Closed 3 ⟨18867354826772957738248214937013657005261,36614060042378982492086463449529039724470,25,7⟩ := by
  apply closed_split (p:=17351) sixPrime3_17351 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_52
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_54 : Closed 3 ⟨252176296062060436488893910621,488438566589025595940610483270,21,6⟩ := by
  apply closed_split (p:=523) sixPrime3_523 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_53
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_55 : Closed 3 ⟨2848507219459519122141,5460375505650216221070,17,5⟩ := by
  apply closed_split (p:=97) sixPrime3_97 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_54
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_56 : Closed 3 ⟨3084398968144221,5721834744290574,13,4⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_55
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_57 : Closed 3 ⟨1284630973821,2042782843374,9,3⟩ := by
  apply closed_split (p:=7) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_56
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_58 : Closed 3 ⟨1521,2379,4,2⟩ := by
  apply closed_split (p:=61) sixPrime3_61 (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase3_28
  · exact sixCase3_42
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_51
  · exact sixCase3_57

theorem sixCase3_59 : Closed 3 ⟨99380686121773248094988752661969009967773116818992444938268082355217885572678193710231682589565276636502913321979582437,165545847029704033468594883363869016788544610422023977322814946990422781423800448962061689760150538242274575842072027250,41,13⟩ := by
  apply closed_split (p:=5) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_60 : Closed 3 ⟨107610640279726447038008613406700020863383850306590153270221340235054628506204183456826301285585575895407806992997,173472681197000993884130213468303128233158801873639955069726080226366603364543252903486505635148656081938767838450,37,12⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_59
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_61 : Closed 3 ⟨23193778805006943551506524230161830936195404788933970784326302065152757677953358056756312396917,37388498882698455562689105013906869006080785391381849596488555605912645988929731968660512089890,33,11⟩ := by
  apply closed_split (p:=46411) sixPrime3_46411 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_60
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_62 : Closed 3 ⟨2474199089439555286161146010843718531217858900277020349621130873387208078277,3988350447457156832557854156905045294228369489584027972628739471739839339690,29,10⟩ := by
  apply closed_split (p:=55333) sixPrime3_55333 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_61
  · exact closed_impossible (by decide +kernel)

theorem sixCase3_63 : Closed 3 ⟨57525982018014916233340122861593244209962402447317726523077,92724084050642798536487200247268765583258512348922666613538,25,9⟩ := by
  apply closed_split (p:=14401) sixPrime3_14401 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase3_62
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
