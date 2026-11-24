module

public import OddPerfect.SixthLeast5.Part001
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase5_16 : Closed 5 ⟨51078126119862317478818008163984827978726148125,92886370295418812022740543050938648248385197090,29,10⟩ := by
  apply closed_split (p:=4933) sixPrime5_4933 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_15
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_17 : Closed 5 ⟨4382628588581004696318177710859183813524699380594642118149957610101330781985308125,8043789820953416800791172464007819452216966727747603535010784281632289871819403050,43,14⟩ := by
  apply closed_split (p:=2467) sixPrime5_2467 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_18 : Closed 5 ⟨888430688948105553682987575686029558792762898965060230721661790006351263325625,1630277628892058532791076705311678040579036629053020578640207596601599082249575,42,13⟩ := by
  apply closed_split (p:=4933) sixPrime5_4933 (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase5_17
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_19 : Closed 5 ⟨74013608202622180689645358284800128115759700288739449637369035375625,135405261450319987093298409861710235464325236599825516065210468808015,38,12⟩ := by
  apply closed_split (p:=331) sixPrime5_331 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_18
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_20 : Closed 5 ⟨47195356521777305507902144505058911683052425041847585875625,85908344157794453642577792387986878407705893611357392014015,34,11⟩ := by
  apply closed_split (p:=199) sixPrime5_199 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_19
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_21 : Closed 5 ⟨2587260322349385967254568567530323491606415580975625,4708412554652945250348823988845318262306652176944655,32,10⟩ := by
  apply closed_split (p:=4271) sixPrime5_4271 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_20
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_22 : Closed 5 ⟨1380489895131413985914000220648238594019625625,2444378165668916105861593238182596006536452555,28,9⟩ := by
  apply closed_split (p:=37) sixPrime5_37 (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase5_16
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_21
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_23 : Closed 5 ⟨403793580009896447881581940758832875625,698353656166864733157208182667965641555,24,8⟩ := by
  apply closed_split (p:=43) sixPrime5_43 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_22
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_24 : Closed 5 ⟨73840924291763765862109825648374346548895567853591504481939826211745050047207831920497568116625625,127706621576230182150947725281742269299657173674545023722267258999667878507202273640061132971148125,34,10⟩ := by
  apply closed_split (p:=59376284620771) sixPrime5_59376284620771 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_25 : Closed 5 ⟨4971846341559205627412520439656264384019478657527309734408565554550725625,8598719232351902116463230250783274186012775119061212341371284254740262125,30,9⟩ := by
  apply closed_split (p:=1963111) sixPrime5_1963111 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_24
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_26 : Closed 5 ⟨3168003315119223581396187155999439967836375625,5479004143425733061695118971326380815371325925,26,8⟩ := by
  apply closed_split (p:=6294091) sixPrime5_6294091 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_25
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_27 : Closed 5 ⟨51467514089729575577649429375625,88980351310561490427696970029185,22,7⟩ := by
  apply closed_split (p:=2801) sixPrime5_2801 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact sixCase5_23
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_26
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_28 : Closed 5 ⟨218396532500289753342398518688924210670625,377651830683524453507516912967272676866650,25,8⟩ := by
  apply closed_split (p:=2557) sixPrime5_2557 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_29 : Closed 5 ⟨42713970760862459092978392076848075625,73846662237685657705810894205567594225,24,7⟩ := by
  apply closed_split (p:=5113) sixPrime5_5113 (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase5_28
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_30 : Closed 5 ⟨62014955748474343434675625,107097757684831356515324945,20,6⟩ := by
  apply closed_split (p:=911) sixPrime5_911 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_27
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_29
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_31 : Closed 5 ⟨12513360168157288756038892259835185645942737974457314225625,21746773278489733351495843197116355920736240684759650718125,32,9⟩ := by
  apply closed_split (p:=104670301) sixPrime5_104670301 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
