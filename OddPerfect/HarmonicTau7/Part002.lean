module

public import OddPerfect.HarmonicTau7.Part001
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htau7_30 : Closed 7 ⟨95367431640625,119209289550781,20,1⟩ := by
  exact closed_size (c:=119209289550781) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htauRoot7_5 : RootAt 7 5 := by
  intro e he hdiv
  have cases := allowed_list (p:=5) (r:=7) (E:=22) [6, 13, 20] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau7_27
  · exact htau7_29
  · exact htau7_30

theorem htau7_32 : Closed 7 ⟨183381411708289950617,251476836276049003620,14,6⟩ := by
  exact closed_size (c:=1357719664593721) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_33 : Closed 7 ⟨66200689626692672172737,90796338779447708627220,16,6⟩ := by
  exact closed_size (c:=1470624210875408303) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_34 : Closed 7 ⟨23898448955236054654358057,32777491500264416832746820,18,6⟩ := by
  exact closed_size (c:=530895553940142805843) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_35 : Closed 7 ⟨8627340072840215730223258577,11832674444796338270639922420,20,6⟩ := by
  exact closed_size (c:=21294810576245074813087) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_36 : Closed 7 ⟨3114469766295317878610596346297,4271595474584678999495030314020,22,6⟩ := by
  exact closed_size (c:=69186839562434062188128123) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_37 : Closed 7 ⟨507981749884459697,660044189700916020,12,5⟩ := by
  apply closed_split (c:=10690706020423) (p:=19) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=19) (r:=1) (E:=12) [2, 4, 6, 8, 10] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · exact htau7_32
  · exact htau7_33
  · exact htau7_34
  · exact htau7_35
  · exact htau7_36

theorem htau7_38 : Closed 7 ⟨61465791736019623337,79924899813031973700,14,5⟩ := by
  exact closed_size (c:=1812356004830657) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_39 : Closed 7 ⟨7437360800058374423777,9670972430236089952980,16,5⟩ := by
  exact closed_size (c:=1096482134947402489) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_40 : Closed 7 ⟨899920656807063305277017,1170187723611426105445860,18,5⟩ := by
  exact closed_size (c:=18953477868665793739) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_41 : Closed 7 ⟨108890399473654659938519057,141592714616535417980084340,20,5⟩ := by
  exact closed_size (c:=16053595761511952151937) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_42 : Closed 7 ⟨13175738336312213852560805897,17132718468660338434811340420,22,5⟩ := by
  exact closed_size (c:=1942485087149698235239381) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_43 : Closed 7 ⟨1594264338693777876159857513537,2073058934707960503471393326100,24,5⟩ := by
  exact closed_size (c:=6715448444146292528252003) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_44 : Closed 7 ⟨4198196280036857,4962738268427940,10,4⟩ := by
  apply closed_split (c:=562668737917) (p:=11) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=11) (r:=1) (E:=15) [2, 4, 6, 8, 10, 12, 14] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htau7_37
  · exact htau7_38
  · exact htau7_39
  · exact htau7_40
  · exact htau7_41
  · exact htau7_42
  · exact htau7_43

theorem htau7_45 : Closed 7 ⟨457603394524017413,540983587061085714,11,4⟩ := by
  exact closed_size (c:=29207622668237) [(571,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime7_571) (by decide +kernel)

theorem htau7_46 : Closed 7 ⟨49878770003117898017,58967256105460783080,12,4⟩ := by
  exact closed_size (c:=3342814971964897) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_47 : Closed 7 ⟨5436785930339850883853,6427430960611027795974,13,4⟩ := by
  exact closed_size (c:=7287336690035178907) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_48 : Closed 7 ⟨592609666407043746339977,700589974751717832201420,14,4⟩ := by
  exact closed_size (c:=3782474758404696211) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_49 : Closed 7 ⟨64594453638367768351057493,76364307247982359512395034,15,4⟩ := by
  exact closed_size (c:=86580847219934647973237) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_50 : Closed 7 ⟨7040795446582086750265266737,8323709490030122302653498960,16,4⟩ := by
  exact closed_size (c:=235932808674323194519657) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_51 : Closed 7 ⟨38515562202173,45115802440254,9,3⟩ := by
  apply closed_split (c:=51151703447) (p:=109) (by decide +kernel) (by decide +kernel) htauPrime7_109 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=109) (r:=1) (E:=8) [1, 2, 3, 4, 5, 6, 7] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact htau7_44
  · exact htau7_45
  · exact htau7_46
  · exact htau7_47
  · exact htau7_48
  · exact htau7_49
  · exact htau7_50

theorem htau7_52 : Closed 7 ⟨2664082921962104237,3120615110530433358,11,3⟩ := by
  exact closed_size (c:=173367506140579631) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_53 : Closed 7 ⟨184271951629196787969053,215849826580451085443934,13,3⟩ := by
  exact closed_size (c:=11991657032247282524663) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_54 : Closed 7 ⟨556832717,649774638,7,2⟩ := by
  apply closed_split (c:=36098591) (p:=263) (by decide +kernel) (by decide +kernel) htauPrime7_263 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=263) (r:=1) (E:=7) [2, 4, 6] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl
  · exact htau7_51
  · exact htau7_52
  · exact htau7_53

theorem htau7_55 : Closed 7 ⟨2635489249561,3075383498911,8,2⟩ := by
  exact closed_size (c:=3075383498911) [(22406023,1)] (by decide +kernel) (by decide +kernel) (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl
    · exact htauPrime7_22406023) (by decide +kernel)

theorem htau7_56 : Closed 7 ⟨12473770618172213,14555790100483020,9,2⟩ := by
  exact closed_size (c:=80865500558239) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_57 : Closed 7 ⟨59038356335809084129,68892554545586270917,10,2⟩ := by
  exact closed_size (c:=68892554545586270917) [] (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)

theorem htau7_58 : Closed 7 ⟨117649,137257,6,1⟩ := by
  apply closed_split (c:=137257) (p:=4733) (by decide +kernel) (by decide +kernel) htauPrime7_4733 (by decide +kernel) (by decide +kernel)
  intro e he
  have cases := allowed_list (p:=4733) (r:=1) (E:=5) [1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel) he (one_dvd _)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl|rfl|rfl|rfl
  · exact htau7_54
  · exact htau7_55
  · exact htau7_56
  · exact htau7_57

theorem htauRoot7_7 : RootAt 7 7 := by
  intro e he hdiv
  have cases := allowed_list (p:=7) (r:=7) (E:=18) [6] (by decide) (by decide +kernel) (by decide +kernel) he hdiv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
  rcases cases with rfl
  · exact htau7_58

end OddPerfect.HarmonicChain
