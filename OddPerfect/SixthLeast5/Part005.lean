module

public import OddPerfect.SixthLeast5.Part004
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixCase5_64 : Closed 5 ⟨1375604686332506965274900569176996266391715153807150200240334878173874732484947565848300937526649786339768981996916137592001175625,2373161125257532705270271633135979678598153864555691794010272400066037914239625962550301468097690231485204936482277777673583500625,40,12⟩ := by
  apply closed_split (p:=171559) sixPrime5_171559 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_65 : Closed 5 ⟨1489521826068391477048059079519573746987578142572989894372011982590406425500825174358028607391331422176397701835601071975625,2486795233450031913560414786819706151176147944897796610109212882742978308024820117834760865863314382178868324573671706292625,36,11⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_64
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_66 : Closed 5 ⟨620375604360013109974202032286369740519607722854223196323203657888549115160693533676813247559904798907287672567930475625,887824074776876798843418345883508086817617973901391149628423021329160409862484868916373033153628840477996545724266942625,32,10⟩ := by
  apply closed_split (p:=7) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_65
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_67 : Closed 5 ⟨337756151948099855042014593929491541268888491008799383987555650208662308128597086541803820130509310014350347108438523019269130269661056480259512491022690530607049940917613125,489562317772158986188797207614405635677848660954308236263942264654892306510924896118566514441169361412317973352475852344926049618184785172739958190610288424114005484269096250,43,13⟩ := by
  apply closed_split (p:=1531042113494635691575231) sixPrime5_1531042113494635691575231 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_68 : Closed 5 ⟨1300041875568930849728162472846333192847115587853728264684012003302153473026318031750192741227831427337829168158147164111347183464162670853813125,1884352015330929085506684740242144309398746713798329072781670161688043674665309892170466120597024061726873618979866043482018518373141364819171250,39,12⟩ := by
  apply closed_split (p:=22576753) sixPrime5_22576753 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_67
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_69 : Closed 5 ⟨33377128935083109319545766101136816450962337866607472900608653504524251773091769225080500891072124531341261348292116879329395578514013125,47766253907905287821611584819215671760691025097119350126701926186686490048498022878713696363835017629955101746051763914272410561486571250,35,11⟩ := by
  apply closed_split (p:=79) sixPrime5_79 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_68
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_70 : Closed 5 ⟨23091745440984884342094852860371744041938683101232189512404747517862810762883482009918611740137535965791642113145694317739350625,33046766164129459429254861275998798855224362790232705078832242572395151174008889419875853082025456339476493650821071144724091875,34,10⟩ := by
  apply closed_split (p:=1445413861) sixPrime5_1445413861 (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase5_69
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_71 : Closed 5 ⟨16666816783886936454246809109605574923406805601157846531514986389132365255904494569700841913134174921770146600625,23848094144309419605922363581372701485147415231400452221215214169959893413956711078567643364072459614342253143375,30,9⟩ := by
  apply closed_split (p:=6101) sixPrime5_6101 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact sixCase5_66
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_70
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_72 : Closed 5 ⟨376203405112712713532195429468826146776713339436140513067202804290482137688641507331781973364106509468370670839454100625,538299204878465958073999778158318100636827973423449937148869358059712632081360513707376747212507133465741890606739249375,32,9⟩ := by
  apply closed_split (p:=31) (by norm_num) (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_73 : Closed 5 ⟨738384549242530002291192930108658728280527969193242837952868528985638679349008294377660266501590839100625,1056311957007698122308480922007371985030239522547837247509206225091796566758590621005936653692958399037375,28,8⟩ := by
  apply closed_split (p:=4751) sixPrime5_4751 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_71
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_72
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_74 : Closed 5 ⟨1080387198413526791768603936939619791585799488191403595134913590537932533824054604252000625,1545268947201904216094339242869418796743793425357274615841950425634009268059139929260979875,24,7⟩ := by
  apply closed_split (p:=5113) sixPrime5_5113 (by decide +kernel)
  intro j
  fin_cases j
  · exact sixCase5_63
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_73
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_75 : Closed 5 ⟨122585278981552825353150800070476056960419448482744099940299211355868005850625,175230958790650852400620924914883699771221048761278078241134225198246085724875,20,6⟩ := by
  apply closed_split (p:=1723) sixPrime5_1723 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_74
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_76 : Closed 5 ⟨69148792637998407241338730730862251307386314517492386097792837692047084623241119780787000625,98847153260081423628302126158993439980679418832146411066904256004934858742738225385017549375,24,7⟩ := by
  apply closed_split (p:=331) sixPrime5_331 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)

theorem sixCase5_77 : Closed 5 ⟨206065853967990299418646494918470251750465092899492831999642974289214117834900625,294567513172394127769831950103362578314488393347306809174702481448244894906533125,22,6⟩ := by
  apply closed_split (p:=579281) sixPrime5_579281 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact sixCase5_76
  · exact closed_impossible (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_78 : Closed 5 ⟨72924020809965987717519809679045839952658803380573527626590845541860800625,101701078810592485432745748644738072995485228532372651329735476029161976625,18,5⟩ := by
  apply closed_split (p:=41) sixPrime5_41 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact sixCase5_75
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_77
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)

theorem sixCase5_79 : Closed 5 ⟨4965126921833223161850625,6924450390600077485150825,14,4⟩ := by
  apply closed_split (p:=1957650063931) sixPrime5_1957650063931 (by decide +kernel)
  intro j
  fin_cases j
  · exact closed_impossible (by decide +kernel)
  · exact closed_smaller (q:=3) (by decide) (by decide) (by decide +kernel)
  · exact closed_impossible (by decide +kernel)
  · exact sixCase5_78
  · exact closed_impossible (by decide +kernel)

end OddPerfect.SixthPowerChain
