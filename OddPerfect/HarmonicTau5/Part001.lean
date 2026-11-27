module

public import OddPerfect.HarmonicTau5.Primes07
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau5_0 : Closed 5 ⟨1675804433437994409,2927661388283831661,12,5⟩ := by
  exact closed_size (c:=108431903269771543) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_1 : Closed 5 ⟨49210937314193864535148449,85972419085533802542869841,14,5⟩ := by
  exact closed_size (c:=9552491009503755838096649) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_2 : Closed 5 ⟨57066998769,99678706281,10,4⟩ := by
  apply closed_split (c:=11075411809) (p:=5419) (by decide +kernel) (by decide +kernel) htauPrime5_5419 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=5419) (r:=1) (E:=5) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_0
  · exact htau5_1

theorem htau5_3 : Closed 5 ⟨920433623145201,1607718638429673,12,4⟩ := by
  exact closed_size (c:=535906212809891) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_4 : Closed 5 ⟨14845673907708946929,25930893920017019241,14,4⟩ := by
  exact closed_size (c:=8643631306672339747) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_5 : Closed 5 ⟨3538161,6131433,8,3⟩ := by
  apply closed_split (c:=2043811) (p:=127) (by decide +kernel) (by decide +kernel) htauPrime5_127 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=127) (r:=1) (E:=8) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_2
  · exact htau5_3
  · exact htau5_4

theorem htau5_6 : Closed 5 ⟨1060038275616441,1839272483311109,12,4⟩ := by
  exact closed_size (c:=1839272483311109) [(151,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_151) (by decide +kernel)

theorem htau5_7 : Closed 5 ⟨879748025737872331161,1526450860640996378165,14,4⟩ := by
  exact closed_exact (c:=305290172128199275633) (p:=11) (e:=3) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem htau5_8 : Closed 5 ⟨1277276121,2213769173,10,3⟩ := by
  apply closed_split (c:=2213769173) (p:=911) (by decide +kernel) (by decide +kernel) htauPrime5_911 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=911) (r:=1) (E:=6) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_6
  · exact htau5_7

theorem htau5_9 : Closed 5 ⟨32664549885281721,56614871508279546,13,4⟩ := by
  exact closed_size (c:=9435811918046591) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_10 : Closed 5 ⟨2313989378423242397361,4010654113317202311499,14,4⟩ := by
  exact closed_size (c:=4010654113317202311499) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_11 : Closed 5 ⟨163925321556880914671450601,284118748041504728119893972,15,4⟩ := by
  exact closed_size (c:=23676562336792060676657831) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_12 : Closed 5 ⟨461096679681,799170993313,12,3⟩ := by
  apply closed_split (c:=799170993313) (p:=70841) (by decide +kernel) (by decide +kernel) htauPrime5_70841 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=70841) (r:=1) (E:=4) [1, 2, 3] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_9
  · exact htau5_10
  · exact htau5_11

theorem htau5_13 : Closed 5 ⟨166455901364841,288500728907853,14,3⟩ := by
  exact closed_size (c:=32055636545317) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_14 : Closed 5 ⟨60090580392707601,104148763136056793,16,3⟩ := by
  exact closed_size (c:=104148763136056793) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_15 : Closed 5 ⟨9801,16093,6,2⟩ := by
  apply closed_split (c:=16093) (p:=19) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=19) (r:=1) (E:=12) [2, 4, 6, 8, 10] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · exact htau5_5
  · exact htau5_8
  · exact htau5_12
  · exact htau5_13
  · exact htau5_14

theorem htau5_16 : Closed 5 ⟨2593190942796613982229,4287330473246302558230,13,5⟩ := by
  exact closed_size (c:=15879001752764083549) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_17 : Closed 5 ⟨54943515758316023579401000461,90838281721859040170852036910,15,5⟩ := by
  exact closed_size (c:=1009314241353989335231689299) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_18 : Closed 5 ⟨122391863225181,202306879099710,11,4⟩ := by
  apply closed_split (c:=2247854212219) (p:=4603) (by decide +kernel) (by decide +kernel) htauPrime5_4603 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=4603) (r:=1) (E:=5) [2, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl
  · exact htau5_16
  · exact htau5_17

theorem htau5_19 : Closed 5 ⟨3921557689598024421,6482115843404759910,13,4⟩ := by
  exact closed_size (c:=72023509371163999) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_20 : Closed 5 ⟨125650629932410300473261,207693473739662083228110,15,4⟩ := by
  exact closed_size (c:=2307705263774023146979) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_21 : Closed 5 ⟨3819851541,6278727510,9,3⟩ := by
  apply closed_split (c:=69763639) (p:=179) (by decide +kernel) (by decide +kernel) htauPrime5_179 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=179) (r:=1) (E:=7) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau5_18
  · exact htau5_19
  · exact htau5_20

theorem htau5_22 : Closed 5 ⟨12303741813561,20223783258415,10,3⟩ := by
  exact closed_size (c:=4044756651683) [(10378063,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime5_10378063) (by decide +kernel)

theorem htau5_23 : Closed 5 ⟨39630352381479981,65140805877303420,11,3⟩ := by
  exact closed_size (c:=361893365985019) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_24 : Closed 5 ⟨127649365020747018801,209818535730796264525,12,3⟩ := by
  exact closed_size (c:=8392741429231850581) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_25 : Closed 5 ⟨1185921,1948705,8,2⟩ := by
  apply closed_split (c:=389741) (p:=3221) (by decide +kernel) (by decide +kernel) htauPrime5_3221 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=3221) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau5_21
  · exact htau5_22
  · exact htau5_23
  · exact htau5_24

theorem htau5_26 : Closed 5 ⟨294714678187442601,484288731327124317,12,3⟩ := by
  exact closed_size (c:=161429577109041439) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_27 : Closed 5 ⟨143496441,235794757,10,2⟩ := by
  apply closed_split (c:=235794757) (p:=45319) (by decide +kernel) (by decide +kernel) htauPrime5_45319 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=45319) (r:=1) (E:=4) [2] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau5_26

theorem htau5_28 : Closed 5 ⟨30782864128631373,50582734874169806,13,3⟩ := by
  exact closed_size (c:=25291367437084903) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau5_29 : Closed 5 ⟨54574724333601660772089,89677776579300061035807,14,3⟩ := by
  exact closed_size (c:=29892592193100020345269) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

end OddPerfect.HarmonicChain
