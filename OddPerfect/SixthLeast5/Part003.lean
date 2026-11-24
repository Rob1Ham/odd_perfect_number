module

public import OddPerfect.SixthLeast5.Part002
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase5_32 : Closed 5 ⟨514256406456517021743279342540881315093175625,893315785745712868312674056284156489800348625,28,8⟩ := by
  apply closed_split (p:=2221) sixPrime5_2221 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_31
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_33 : Closed 5 ⟨619645010135322544848581181270122475625,1075204987940672636152721493108911766625,26,7⟩ := by
  apply closed_split (p:=911) sixPrime5_911 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_32
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_34 : Closed 5 ⟨312617391928059165254199825625,539881304613340737127386746825,22,6⟩ := by
  apply closed_split (p:=211) sixPrime5_211 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_33
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_35 : Closed 5 ⟨12302113816400385525625,20946168137068522690265,18,5⟩ := by
  apply closed_split (p:=71) sixPrime5_71 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_30
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_34
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_36 : Closed 5 ⟨23663117025625,40023135382153,14,4⟩ := by
  apply closed_split (p:=151) sixPrime5_151 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_35
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_37 : Closed 5 ⟨181575625,290948273,10,3⟩ := by
  apply closed_split (p:=19) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_36
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_38 : Closed 5 ⟨75625,103873,6,2⟩ := by
  apply closed_split (p:=7) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_37
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_39 : Closed 5 ⟨1387065783552680931338318638850101225326933300212275330381370581365494543386228356023500630322171322270170073240117063123960579436386090897130303457592482158471529882513635868540631469549510903485713105533245224315822784874147113399061156789770625,1939341721715980737751143892414044909087971948400281005628371476602938143918316873504215413642393128893215126778798572394159859815942835549388503504671298492748974133890329089193559000066896727435646349018201892197780347219636285007985094102661250,35,11⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_40 : Closed 5 ⟨5110008375863192853468409852786061152614871372461327987965600559110431155891071562599241199089936016556710567821799444903167095009177283082254720022371278320045718526359819881818264262029357773828246674353709367103063961870708969533199320625,7130902812941395475675528996275393745060805875800314769392790477391917812049127541261919502441115625630012636935166079187830182105443885930764491878201440978180760375088997728343778381864065065599535043436797991630406883361473012902435603750,33,10⟩ := by
  apply closed_split (p:=521) sixPrime5_521 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_39
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_41 : Closed 5 ⟨4990199116324343013714256279740631319866848777726800702039699449223761092454266607341395227757527816250041248752167838925944068613882322485415370470625,6963711661181748539076997375447919848588412221615768920621411483213862125500171344863606394082148895849903367798262552621536846251780262913761657150750,29,9⟩ := by
  apply closed_split (p:=31810898376456201755581) sixPrime5_31810898376456201755581 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_40
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_42 : Closed 5 ⟨1465545663083090826504759976795339753682074742081823965989246551072238951598220625,2045136313422955579327792429621871024571902269713350016196820603597438260159540150,25,8⟩ := by
  apply closed_split (p:=241562563680036301) sixPrime5_241562563680036301 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_41
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_43 : Closed 5 ⟨34282812426179414056072947111053785034158154020473229925631686970625,47822190977327860503460805489514833530327171349299168757962292615150,21,7⟩ := by
  apply closed_split (p:=2557) sixPrime5_2557 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_42
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_44 : Closed 5 ⟨3066636519023416981847243376016153698448573420298587159845349919079827762727239436213088823339447867104761118030067756637477795056168665699754287061252294283374819119910776255694893121939014364857061600215286674993807503910879214659492800319721538317017107127442595625,4309205878797391123794342828971276836890062868640568140964321174066260436627084584559000104581073709984929412323132730942821014294685470961298635109591748202683872126896061029310416856267601402430625558169061238614637440286865711780923780110782794142243489139469671250,41,13⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_45 : Closed 5 ⟨11297617231823552749390266673111850083254089913825056494211817371288153826161999978680777124087547080598587236379425940213445260871307819009487465273309095838045170478707255925578277128138396059759069559187030238592576301704161179259923152065168999219046154145625,15844824034142111698261685703464356684144765532960616484464140982656686522163252297404426721947741825119333925288119085841901340603999334325987855368530822952695300930259119914511962495882165597638743351739248495621233183509763136091761673870279391469587734873750,39,12⟩ := by
  apply closed_split (p:=521) sixPrime5_521 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_44
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_46 : Closed 5 ⟨11032733291223458452265128624079226050961055120595839772268949229385228633953036895280171262645143784494466145124724363208470419743691163846328120137645558880504784931295625,15473326280044347858768969925873894428780642945425232950832221517345212058435941238850607579857808450101927520669765413588942715818197069762366091896475732980546265261564750,35,11⟩ := by
  apply closed_split (p:=31810898376456201755581) sixPrime5_31810898376456201755581 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_45
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_47 : Closed 5 ⟨3240146144471814230704852187399070200250666912139404314337096192642300855172189892570473551031869045625,4544280838214693612911669743047422788093440989095414860965795597943759458241541261941871585942653142950,31,10⟩ := by
  apply closed_split (p:=241562563680036301) sixPrime5_241562563680036301 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_46
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
