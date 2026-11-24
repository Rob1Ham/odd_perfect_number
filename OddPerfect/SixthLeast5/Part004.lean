module

public import OddPerfect.SixthLeast5.Part003
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase5_48 : Closed 5 ⟨2335260659650068015762863658378455555559551763027754150889479434598945303003157208975729045625,3258215810444702340491166760334287789909084044932730545235648623935659114683243163571202867950,27,9⟩ := by
  apply closed_split (p:=193) sixPrime5_193 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_47
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_49 : Closed 5 ⟨50175644714216414700706089623498721321474736258960995458694321963989205912425509713737835114489121023351869584872166062470916026483191104281915188313426509261182982578834051000223548157850358469722624257939003166936408154950625,70546692498790514449728207398693727162435803118666623182990574659178893367905595108691862430209439839233972430915569569601668069086367674382263455492189578648070915706429373149465367023302515036152293657525338046725186672794375,40,12⟩ := by
  apply closed_split (p:=1471) sixPrime5_1471 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_50 : Closed 5 ⟨796426163302430353497660189893790913183516710194457158754532816367822826819026836300024366509882716518021453387599658139885335573771703691717832864770821245078379431736544673897613500703962769951629724257376917301890575625,1115309827182750453729122846326557272578941759579255105417775831330986567718615640502298111239141856342528772246621813504524181763495291517908454231296374537936080750421788265370264920609338925207536301163981756544751816875,38,11⟩ := by
  apply closed_split (p:=251) sixPrime5_251 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_49
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_51 : Closed 5 ⟨147661866937557680896995257035043937297190895517566517008190874229734670166503599874627395313336516896598701812826376204746825131090818275993726265632193733289057308818999464540967419876711536540364775963630775625,206021639369297130827619703731644438843823242002829469838863696049709442864072787153394768262456365337458633352695584908355399181783446658828053087013221659407385989581462833383263678330554944322419598847442340875,34,10⟩ := by
  apply closed_split (p:=271) sixPrime5_271 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_50
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_52 : Closed 5 ⟨26873226219253666086301870995710209595701584440703369853944401432918106025071041415527214526502992119208043191575625,37494217265814774384099861028065902536035302233058163145344380599138477394121187416717566734302060933034602333697675,30,9⟩ := by
  apply closed_split (p:=1531042113494635691575231) sixPrime5_1531042113494635691575231 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_51
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_53 : Closed 5 ⟨103436515412560345403205840023959847350925607549843600224065853694680776416482795775625,144317283629201183681727087974395601329982336917553805353756728001539066009367119984175,26,8⟩ := by
  apply closed_split (p:=22576753) sixPrime5_22576753 (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase5_48
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_52
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_54 : Closed 5 ⟨2156208321086888128411001322633430838335687905696770835325647876635177690138952713549080059308475625,3108677042996873372484923069018798111332603136340442654556169624568181078021394833485741924072549375,32,9⟩ := by
  apply closed_split (p:=241562563680036301) sixPrime5_241562563680036301 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_55 : Closed 5 ⟨2334769129328827529001507624226661698364940164540677294101214673662188179953626082730203275625,3257529870425988936959277242620334286556816883847871125642399049117610279754789960741840317375,28,8⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_54
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_56 : Closed 5 ⟨4582514213629546862203569813059987342324041521610937383179535287752325388275625,6392295811058445104206397083513098687396825261699669804322912511003644590050975,24,7⟩ := by
  apply closed_split (p:=4751) sixPrime5_4751 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_53
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_55
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_57 : Closed 5 ⟨6705028833596599658922931177597063374566429497452225684653175625,9351230148089139715185922074602040189739376485979501125921449475,20,6⟩ := by
  apply closed_split (p:=5113) sixPrime5_5113 (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase5_43
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_56
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_58 : Closed 5 ⟨5551548215717150474497934616661419863237175625,7742284239436528944098713456257222938538651395,16,5⟩ := by
  apply closed_split (p:=33151) sixPrime5_33151 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_57
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_59 : Closed 5 ⟨478573784584575625,667427133619962595,12,4⟩ := by
  apply closed_split (p:=10378063) sixPrime5_10378063 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_58
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_60 : Closed 5 ⟨38366222835203513779080485501860215854394733774291362638746185921876573065388306024468627967369990367495016563961658007500538774634096576087601704270625,54916100670605081991837320737473941583546562136129007221752046644088613061743866338685272179585521580462202200784698382511671627959707083907411218561250,35,11⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_61 : Closed 5 ⟨1030734932499115615948677658848282933467441481343120000849659210691935521636356378400853511251792723581687621426837655502976268776639419471395625,1475116947194855537515027766306563626699464709313476019085587829348241123473822224415796556173552191741380266534972017996943659450706283439978750,33,10⟩ := by
  apply closed_split (p:=6101) sixPrime5_6101 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_60
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_62 : Closed 5 ⟨236144662816627609001551481809812460658792758182574761165795332047463790284205282142658448699639269240445625,337954000476959392927445076537921538005154337951409166114649006971902491762359411246155257686550300133205750,29,9⟩ := by
  apply closed_split (p:=1445413861) sixPrime5_1445413861 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_61
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_63 : Closed 5 ⟨5524019745488362486312871929572275994378192783122646581924813188420449045442391191540479195625,7902505395990538161106450888034207726547759577277102385415734476692323396854441598240651080750,25,8⟩ := by
  apply closed_split (p:=2557) sixPrime5_2557 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_62
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
