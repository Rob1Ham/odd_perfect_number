module

public import OddPerfect.SizeIndex300.Seed7Part04

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state7_172 : State := ⟨1354298909791393318719894881240019517653027924452740603039549105705721929, 1580128381834351951806924094860112393493550392771595680797951233611724774, 16148168401⟩

private noncomputable def tree7_172 : AbundanceTree :=
  .split 487880282891 [
    (2, .split 1552757273887 [
      (2, .split 19038018253 [
        (2, .split 133539253321 [
          (2, .round 1 [(3671, 1), (3823, 1), (341017, 1), (2324557, 1), (16668401, 1), (18160339, 1), (47650987, 1), (90739349695786069, 1)]),
          (4, .abundant [(3, 6), (5, 2), (7, 12)])]),
        (4, .round 1 [(241, 1), (709, 1), (1867, 1), (3217, 1), (3671, 1), (3823, 1), (2324557, 1), (16668401, 1), (18160339, 1), (47650987, 1)]),
        (6, .round 1 [(77169425877976810466138299806024985584499711073406042088379, 1)])]),
      (4, .round 1 [(3217, 1), (3671, 1), (3823, 1), (16668401, 1), (47650987, 1), (141785047417170330875956138182105901767368657881, 1)]),
      (6, .round 1 [(3217, 1), (3671, 1), (3823, 1), (16668401, 1), (47650987, 1)])]),
    (4, .abundant [(3, 4), (5, 2), (7, 12)]),
    (6, .round 1 [(118215356492453115070073828934796723361084560624588003047719992243, 1)])]

private theorem checked7_172 : replayAbundance bank 7 2413 (10^300) 7 state7_172 tree7_172 = true := by
  decide +kernel

theorem reject7_172 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_172 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree7_172 checked7_172

@[expose] noncomputable def state7_173 : State := ⟨233996737425836946430404611547141449729735271411315019626173152145730474196153095169, 273015715651841127672621235660192008052046670133630023846301341153301696813418561994, 16148168401⟩

private noncomputable def tree7_173 : AbundanceTree :=
  .split 320914928276001699605826186467 [
    (2, .split 16073 [
      (2, .split 258357403 [
        (2, .split 2612510473 [
          (2, .round 1 [(2275070324715731401, 1)])]),
        (4, .round 1 [(53454996722401, 1)])]),
      (4, .split 3823 [
        (2, .split 4873051 []),
        (4, .round 1 [(37, 1), (41, 1), (97, 1), (103, 1), (709, 1), (1867, 1), (5211310507321, 1)]),
        (6, .round 1 [(31330106658892441, 1)])]),
      (6, .round 1 [(103, 1), (421, 1), (709, 1), (1867, 1), (3823, 1), (1050323, 1), (192091292916307, 1)])])]

private theorem checked7_173 : replayAbundance bank 7 2413 (10^300) 7 state7_173 tree7_173 = true := by
  decide +kernel

theorem reject7_173 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_173 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree7_173 checked7_173

@[expose] noncomputable def state7_174 : State := ⟨6985545870247328452034663873384590912350573472182623761314641812949236846974449084819199606499195331788849, 8150386308650116278070941871999709140527285969180275624637199383078796483059749925825654387911340059978034, 16148168401⟩

private noncomputable def tree7_174 : AbundanceTree :=
  .abundant [(3, 4), (7, 12), (11, 2), (23, 2)]

private theorem checked7_174 : replayAbundance bank 7 2413 (10^300) 3 state7_174 tree7_174 = true := by
  decide +kernel

theorem reject7_174 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_174 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_174 checked7_174

@[expose] noncomputable def state7_175 : State := ⟨1206967628016613610485800594488833267556371741713565006315632605137063084087586464707721059960619808595578803958277289, 1408229594807917111811183945507230359283595055654815353392572821703137764869192418061707629588727530794838191276060854, 16148168401⟩

private noncomputable def tree7_175 : AbundanceTree :=
  .split 3823 [
    (2, .split 4873051 [
      (4, .abundant [(3, 4), (5, 2), (7, 12)]),
      (6, .round 1 [(11694467278054166467, 1)])]),
    (4, .split 5211310507321 [
      (2, .abundant [(3, 4), (7, 12), (13, 2), (37, 2), (41, 2), (103, 2)])]),
    (6, .split 31330106658892441 []),
    (10, .round 1 [(42307, 1), (85009, 1), (185472470830161498451637291, 1)]),
    (12, .round 1 [(269241011172102382687, 1)])]

private theorem checked7_175 : replayAbundance bank 7 2413 (10^300) 5 state7_175 tree7_175 = true := by
  decide +kernel

theorem reject7_175 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_175 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_175 checked7_175

@[expose] noncomputable def state7_176 : State := ⟨36031817461069937104500802408255148541871087382281065182988408416779201845504899035495804342867133968472692105778637062028507561838738657369, 42040126450431122867788170309689294355700714960104030242873931282714917515923207734802615734485348050302270194510784812798928624763998336094, 16148168401⟩

private noncomputable def tree7_176 : AbundanceTree :=
  .split 3823 [
    (2, .split 4873051 []),
    (4, .split 5211310507321 []),
    (6, .round 1 [(1867, 1), (31330106658892441, 1)])]

private theorem checked7_176 : replayAbundance bank 7 2413 (10^300) 4 state7_176 tree7_176 = true := by
  decide +kernel

theorem reject7_176 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_176 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_176 checked7_176

@[expose] noncomputable def state7_177 : State := ⟨6225603275950632915720787282798601435037129331469855559300150976596442447367191917693821883765443479156229293269853026201874402772411845787365540357009, 7263723214460665306903396199055391869737716701767501832571802953888488604600139475792061339304149490528845689000521483643199007616697729538430223952514, 16148168401⟩

private noncomputable def tree7_177 : AbundanceTree :=
  .split 4561 [
    (2, .split 3823 [
      (2, .round 1 [(709, 1), (1867, 1), (4873051, 1)])]),
    (4, .abundant [(3, 4), (5, 2), (7, 12)])]

private theorem checked7_177 : replayAbundance bank 7 2413 (10^300) 5 state7_177 tree7_177 = true := by
  decide +kernel

theorem reject7_177 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_177 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_177 checked7_177

@[expose] noncomputable def state7_178 : State := ⟨45365320373930028334279426973887549006109811402649, 52929864525036316416966186010688810718076235231934, 16148168401⟩

private theorem checked7_178 : checkChildren bank 7 2413 (10^300) state7_178 415669 [state7_171, state7_172, state7_173, state7_174, state7_175, state7_176, state7_177] = true := by
  decide +kernel

theorem reject7_178 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_178 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_171, state7_172, state7_173, state7_174, state7_175, state7_176, state7_177] ?_ checked7_178
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_171 ho hN hs hav hx hvalid
  · exact reject7_172 ho hN hs hav hx hvalid
  · exact reject7_173 ho hN hs hav hx hvalid
  · exact reject7_174 ho hN hs hav hx hvalid
  · exact reject7_175 ho hN hs hav hx hvalid
  · exact reject7_176 ho hN hs hav hx hvalid
  · exact reject7_177 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_179 : State := ⟨14651040558917380705879375746776912316245914389705300071809, 17094061841566639453514526011884973229494535444017963657190, 16148168401⟩

private noncomputable def tree7_179 : AbundanceTree :=
  .abundant [(3, 2), (5, 2), (7, 12)]

private theorem checked7_179 : replayAbundance bank 7 2413 (10^300) 3 state7_179 tree7_179 = true := by
  decide +kernel

theorem reject7_179 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_179 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_179 checked7_179

@[expose] noncomputable def state7_180 : State := ⟨493516793752524455458095768866592127057300911932582942038001992110399903043265429689, 575809380796685469224334239215647524102475762193580872713951517017253116079862117598, 16148168401⟩

private noncomputable def tree7_180 : AbundanceTree :=
  .split 3823 [
    (2, .split 4873051 [
      (4, .abundant [(3, 4), (5, 2), (7, 12)]),
      (6, .split 11694467278054166467 [
        (2, .round 1 [(45586854972493208415830044978733809519, 1)])]),
      (10, .round 1 [(54012590136368020642718575079167, 1)])]),
    (4, .split 5211310507321 [
      (2, .abundant [(3, 4), (7, 12), (13, 2), (23, 2), (41, 2)]),
      (4, .abundant [(3, 2), (5, 2), (7, 12)])]),
    (6, .split 31330106658892441 [
      (4, .abundant [(3, 2), (5, 2), (7, 12)])]),
    (10, .split 185472470830161498451637291 [
      (2, .round 1 [(374356982031375302506456579084978889473197343303, 1)])]),
    (12, .split 269241011172102382687 [
      (2, .abundant [(3, 4), (7, 12), (13, 2), (23, 2), (67, 2)])]),
    (16, .round 1 [(12349039, 1), (562036049, 1), (20684330947348876681304004802879337, 1)]),
    (18, .round 1 [(153434889660683954432261024327561, 1), (198365825664557519812628544069833, 1)]),
    (22, .round 1 [(22166774335246803260289460843, 1)])]

private theorem checked7_180 : replayAbundance bank 7 2413 (10^300) 6 state7_180 tree7_180 = true := by
  decide +kernel

theorem reject7_180 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_180 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_180 checked7_180

@[expose] noncomputable def state7_181 : State := ⟨159384624690763833909991817388620743789896528504166191931079225323681675933559289496867052449, 185961578640263602411293706225223842153606932440051402344408652617572494804251489554677284614, 16148168401⟩

private noncomputable def tree7_181 : AbundanceTree :=
  .split 371917347076222464250023584385246226969 [
    (2, .split 4267927 [
      (2, .round 1 [(447331, 1), (13573249, 1)])])]

private theorem checked7_181 : replayAbundance bank 7 2413 (10^300) 5 state7_181 tree7_181 = true := by
  decide +kernel

theorem reject7_181 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_181 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_181 checked7_181

@[expose] noncomputable def state7_182 : State := ⟨16623995049111325317041389097679638182711198580235815841678236185731069006697412898682029677451477780755589169, 19396001142761502504428391948564765608064266639167468973546272277147268045920086337036176845261500832226156566, 16148168401⟩

private noncomputable def tree7_182 : AbundanceTree :=
  .split 3823 [
    (2, .split 4873051 [
      (4, .abundant [(3, 4), (5, 2), (7, 12)]),
      (6, .round 1 [(1862687, 1), (4580731, 1), (11694467278054166467, 1)])]),
    (4, .split 5211310507321 [
      (2, .split 3144784374425079307 [])]),
    (6, .split 31330106658892441 []),
    (10, .round 1 [(103, 1), (709, 1), (1867, 1), (42307, 1), (85009, 1), (185472470830161498451637291, 1)]),
    (12, .round 1 [(22260629, 1), (269241011172102382687, 1)])]

private theorem checked7_182 : replayAbundance bank 7 2413 (10^300) 5 state7_182 tree7_182 = true := by
  decide +kernel

theorem reject7_182 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_182 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_182 checked7_182

@[expose] noncomputable def state7_183 : State := ⟨5368832925860633481715010489238456377511389508796644119286159296995595321956004312631001368097978194854515671114055129, 6264071257098644865243781974418311184685879678767212649662016661953358182835887236544239031185686065387546861783464702, 16148168401⟩

private noncomputable def tree7_183 : AbundanceTree :=
  .split 3823 [
    (2, .split 4873051 [
      (4, .abundant [(3, 4), (5, 2), (7, 12)]),
      (6, .round 1 [(11694467278054166467, 1)])]),
    (4, .split 5211310507321 [
      (2, .round 1 [(41, 1), (103, 1), (709, 1), (1867, 1), (4519, 1), (3144784374425079307, 1)])]),
    (6, .split 31330106658892441 []),
    (10, .round 1 [(185472470830161498451637291, 1)]),
    (12, .round 1 [(269241011172102382687, 1)])]

private theorem checked7_183 : replayAbundance bank 7 2413 (10^300) 5 state7_183 tree7_183 = true := by
  decide +kernel

theorem reject7_183 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_183 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_183 checked7_183

@[expose] noncomputable def state7_184 : State := ⟨559975293427315557797611101489878143141253816920937531948608290211942644857077647030069256966281885303068111537807648708392075676662249, 653349655070730759089155035747515448806338549763588696490324096341260078826790416075521865495417809061631000334007659209264649968273294, 16148168401⟩

private noncomputable def tree7_184 : AbundanceTree :=
  .split 3823 [
    (2, .split 4873051 [
      (4, .abundant [(3, 4), (5, 2), (7, 12)])]),
    (4, .split 5211310507321 []),
    (6, .round 1 [(709, 1), (1867, 1), (31330106658892441, 1)])]

private theorem checked7_184 : replayAbundance bank 7 2413 (10^300) 5 state7_184 tree7_184 = true := by
  decide +kernel

theorem reject7_184 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_184 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_184 checked7_184

@[expose] noncomputable def state7_185 : State := ⟨18862633700421542387817092871952007056376451918509352488079635896673538392479083831461680964988202882700541560860233880750750916474172982165322301301583762600929, 22007926718459035641832139293145861565660332929533944975780178480725970495695043999879624355295647401485263738721016964713895758360417339012643567731076915910982, 16148168401⟩

private noncomputable def tree7_185 : AbundanceTree :=
  .round 1 [(4409, 1), (55681, 1)]

private theorem checked7_185 : replayAbundance bank 7 2413 (10^300) 3 state7_185 tree7_185 = true := by
  decide +kernel

theorem reject7_185 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_185 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_185 checked7_185

@[expose] noncomputable def state7_186 : State := ⟨140468677590049960682763264252660772731889, 163882328883138997024409411178105738908118, 16148168401⟩

private theorem checked7_186 : checkChildren bank 7 2413 (10^300) state7_186 17971 [state7_178, state7_179, state7_180, state7_181, state7_182, state7_183, state7_184, state7_185] = true := by
  decide +kernel

theorem reject7_186 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_186 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_178, state7_179, state7_180, state7_181, state7_182, state7_183, state7_184, state7_185] ?_ checked7_186
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_178 ho hN hs hav hx hvalid
  · exact reject7_179 ho hN hs hav hx hvalid
  · exact reject7_180 ho hN hs hav hx hvalid
  · exact reject7_181 ho hN hs hav hx hvalid
  · exact reject7_182 ho hN hs hav hx hvalid
  · exact reject7_183 ho hN hs hav hx hvalid
  · exact reject7_184 ho hN hs hav hx hvalid
  · exact reject7_185 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_187 : State := ⟨7221702760393942227486677402927472921216352008892009, 8425433250885721128186987099294003931546178868017730, 16148168401⟩

private noncomputable def tree7_187 : AbundanceTree :=
  .abundant [(3, 2), (5, 2), (7, 12)]

private theorem checked7_187 : replayAbundance bank 7 2413 (10^300) 3 state7_187 tree7_187 = true := by
  decide +kernel

theorem reject7_187 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_187 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_187 checked7_187

@[expose] noncomputable def state7_188 : State := ⟨371278434838598636935438313480155988104254284812987864475581729, 433164002177139578274827263808517998944738464765189466581268302, 16148168401⟩

private noncomputable def tree7_188 : AbundanceTree :=
  .split 1949751789915161 [
    (2, .split 681431768085039523 [
      (2, .split 28905399097 [
        (4, .round 1 [(219805483900912246504395259081, 1)])]),
      (4, .round 1 [(94907, 1), (3727678613, 1), (28905399097, 1)])]),
    (4, .abundant [(3, 2), (5, 2), (7, 12)]),
    (6, .split 3727678613 [])]

private theorem checked7_188 : replayAbundance bank 7 2413 (10^300) 6 state7_188 tree7_188 = true := by
  decide +kernel

theorem reject7_188 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_188 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_188 checked7_188

@[expose] noncomputable def state7_189 : State := ⟨981341025922521504869939701101039013210202425963848773377298567089719319663225861969, 1144913268323839100847312199279526815360681496229006255278102656070419589141076083526, 16148168401⟩

private noncomputable def tree7_189 : AbundanceTree :=
  .split 76367962041314001170900173 [
    (2, .round 1 [(103, 1), (709, 1), (10253, 1), (17971, 1), (66529, 1), (4574149, 1), (41423623, 1), (6894921691421288911, 1), (6743275391512125264584053, 1)])]

private theorem checked7_189 : replayAbundance bank 7 2413 (10^300) 4 state7_189 tree7_189 = true := by
  decide +kernel

theorem reject7_189 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_189 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_189 checked7_189

@[expose] noncomputable def state7_190 : State := ⟨50452195588224844919436554308766862097099231098620714402432041756821514032466127694049160908489, 58861686833816930514499642202959894698547856934644327936661553869387587823329040362123238473778, 16148168401⟩

private noncomputable def tree7_190 : AbundanceTree :=
  .split 395638304186730907750217116439 [
    (2, .round 1 [(103, 1), (709, 1), (17971, 1), (113413873, 1), (6458686391, 1), (63716791273521829, 1)])]

private theorem checked7_190 : replayAbundance bank 7 2413 (10^300) 4 state7_190 tree7_190 = true := by
  decide +kernel

theorem reject7_190 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_190 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_190 checked7_190

@[expose] noncomputable def state7_191 : State := ⟨133352235769135137791110429066841853194206496101887212557321799735621552945337065689980022177767914409751710127454329, 155579701713994940461288775868345074838373679844277419083088435938858649792235570833314867697009829191265913970083562, 16148168401⟩

private noncomputable def tree7_191 : AbundanceTree :=
  .round 1 [(1429, 1), (9419, 1), (17971, 1), (46606997, 1), (77802704076084449584930555458000095572679876183121191619769389727643531, 1)]

private theorem checked7_191 : replayAbundance bank 7 2413 (10^300) 3 state7_191 tree7_191 = true := by
  decide +kernel

theorem reject7_191 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_191 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_191 checked7_191

@[expose] noncomputable def state7_192 : State := ⟨6855835946353942620280001953951732419912926693149474676786575335136778271025036379888462121460275550485777327125014334075049649, 7998582891256674154455269313433072161832577574122419557305709491320511946526723630592202725843612121099121537327378592465792694, 16148168401⟩

private noncomputable def tree7_192 : AbundanceTree :=
  .round 1 [(1305845944691541137, 1), (110586159514978869081664464533867414358272338930558694582941, 1)]

private theorem checked7_192 : replayAbundance bank 7 2413 (10^300) 3 state7_192 tree7_192 = true := by
  decide +kernel

theorem reject7_192 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_192 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_192 checked7_192

@[expose] noncomputable def state7_193 : State := ⟨18120936876056976134234959002168217124217872483701788823146685223527348530898254909615405300524226635445624711270796049544846337742837847413157125089, 21141377478183994232076864428010007672771565145257320029745828580953912602420915290211793894668025075558924489953801934284660690752351489352770043438, 16148168401⟩

private noncomputable def tree7_193 : AbundanceTree :=
  .split 17971 [
    (2, .round 1 [(103, 1), (277, 1), (709, 1), (415669, 1)])]

private theorem checked7_193 : replayAbundance bank 7 2413 (10^300) 4 state7_193 tree7_193 = true := by
  decide +kernel

theorem reject7_193 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_193 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_193 checked7_193

@[expose] noncomputable def state7_194 : State := ⟨2732243355695943652574253373369, 3187646079514657499776194726666, 16148168401⟩

private theorem checked7_194 : checkChildren bank 7 2413 (10^300) state7_194 226741 [state7_186, state7_187, state7_188, state7_189, state7_190, state7_191, state7_192, state7_193] = true := by
  decide +kernel

theorem reject7_194 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_194 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_186, state7_187, state7_188, state7_189, state7_190, state7_191, state7_192, state7_193] ?_ checked7_194
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_186 ho hN hs hav hx hvalid
  · exact reject7_187 ho hN hs hav hx hvalid
  · exact reject7_188 ho hN hs hav hx hvalid
  · exact reject7_189 ho hN hs hav hx hvalid
  · exact reject7_190 ho hN hs hav hx hvalid
  · exact reject7_191 ho hN hs hav hx hvalid
  · exact reject7_192 ho hN hs hav hx hvalid
  · exact reject7_193 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_195 : State := ⟨33399426302401629364519925649107887738561, 38966349790526247737725507080393468349282, 16148168401⟩

private noncomputable def tree7_195 : AbundanceTree :=
  .split 149431854123332538041 [
    (2, .split 39138809401289881 [
      (2, .split 3493438662658369039 [
        (2, .round 1 [(709, 1), (8353, 1), (8419, 1), (12301, 1), (249470743, 1), (12246841879, 1), (17361223741, 1), (1277145555272848697640965209, 1)])]),
      (4, .round 1 [(8922316471, 1), (12246841879, 1), (21159749070402571, 1), (154422870697579351637039094511, 1)])]),
    (4, .split 12788156261717729652733923970165403051774558024219019863930028101 []),
    (6, .round 1 [(225125969270404416482117631926997172293796262465095213858155519428636610627186121847177557660897, 1)])]

private theorem checked7_195 : replayAbundance bank 7 2413 (10^300) 6 state7_195 tree7_195 = true := by
  decide +kernel

theorem reject7_195 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_195 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_195 checked7_195

@[expose] noncomputable def state7_196 : State := ⟨408280497783630827065838580861417016689954869401609, 476331555675348931985492524927030492101547173080186, 16148168401⟩

private noncomputable def tree7_196 : AbundanceTree :=
  .split 3185771676889584931 [
    (2, .split 504386079002284537137887203783 [
      (2, .round 1 [(36107, 1), (65119, 1), (140533, 1), (1730648412865978356861379845110213915984712737729472494659, 1)])]),
    (4, .round 1 [(113, 1), (709, 1), (36107, 1), (140533, 1), (14373901, 1), (54544779798968531, 1), (217157768688721808489551017423654592466781186011, 1)]),
    (6, .round 1 [(2213, 1), (36107, 1), (140533, 1)])]

private theorem checked7_196 : replayAbundance bank 7 2413 (10^300) 5 state7_196 tree7_196 = true := by
  decide +kernel

theorem reject7_196 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_196 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_196 checked7_196

@[expose] noncomputable def state7_197 : State := ⟨61009559973105016731706848789660328857313004910452060738949446806780249, 71178463754245830522345019620675243886539880214485522461333788162332906, 16148168401⟩

private noncomputable def tree7_197 : AbundanceTree :=
  .split 32114688199831920912408257521477051711 [
    (2, .round 1 [(3052008943183860449707, 1), (112642002625382695593052618631707887320891012076545473, 1)])]

private theorem checked7_197 : replayAbundance bank 7 2413 (10^300) 4 state7_197 tree7_197 = true := by
  decide +kernel

theorem reject7_197 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_197 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_197 checked7_197

@[expose] noncomputable def state7_198 : State := ⟨745791657912054604950090513034131317350531721850531988263654948910733712869885281, 870098137313453157435527228718911432546298852817932703884599724500362966537035842, 16148168401⟩

private noncomputable def tree7_198 : AbundanceTree :=
  .split 62535446323306841021182891 [
    (2, .round 1 [(38707, 1), (27829610537, 1), (54906848719315955077, 1), (326967446565838722192347285062513589036663371, 1)])]

private theorem checked7_198 : replayAbundance bank 7 2413 (10^300) 4 state7_198 tree7_198 = true := by
  decide +kernel

theorem reject7_198 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_198 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_198 checked7_198

@[expose] noncomputable def state7_199 : State := ⟨111444022253886755341253852971762030782026983115177089434330250259681265037110993924031470244807061041, 130019201943474242458191377968658599727591926344017887184571877298794623540262703089434042455850774322, 16148168401⟩

private noncomputable def tree7_199 : AbundanceTree :=
  .split 378113344089458052918622653774119 [
    (2, .round 1 [(55433533, 1), (15763894763854283, 1)])]

private theorem checked7_199 : replayAbundance bank 7 2413 (10^300) 4 state7_199 tree7_199 = true := by
  decide +kernel

theorem reject7_199 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_199 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_199 checked7_199

@[expose] noncomputable def state7_200 : State := ⟨1362311450168685945376693085079925624034323306133099651019593083164401989347437142222844434197779267425969364729, 1589377733925177874502144987958850458613818899844887827445683794601019168541904579315573600071604082991509983946, 16148168401⟩

private noncomputable def tree7_200 : AbundanceTree :=
  .round 1 [(709, 1), (1483, 1), (4109977401253499170760824214760742307842477719376975414037484928404143775949945401911431, 1)]

private theorem checked7_200 : replayAbundance bank 7 2413 (10^300) 3 state7_200 tree7_200 = true := by
  decide +kernel

theorem reject7_200 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_200 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_200 checked7_200

@[expose] noncomputable def state7_201 : State := ⟨203570884654795771296817672677214112860196511799508229468644197187570918283540724565358206362287220852005088664772128387194512458569, 237501513553101166106375647061952074319332419347943421014743741460911622989578540704119507134603824518337832526773843682612224606266, 16148168401⟩

private noncomputable def tree7_201 : AbundanceTree :=
  .round 1 [(230990058413659785310987191671484258651889186076041880964998692171147028930473596997757, 1)]

private theorem checked7_201 : replayAbundance bank 7 2413 (10^300) 3 state7_201 tree7_201 = true := by
  decide +kernel

theorem reject7_201 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_201 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_201 checked7_201

@[expose] noncomputable def state7_202 : State := ⟨223511436608353935601, 260763342723203065202, 16148168401⟩

private theorem checked7_202 : checkChildren bank 7 2413 (10^300) state7_202 110563 [state7_194, state7_195, state7_196, state7_197, state7_198, state7_199, state7_200, state7_201] = true := by
  decide +kernel

theorem reject7_202 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_202 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_194, state7_195, state7_196, state7_197, state7_198, state7_199, state7_200, state7_201] ?_ checked7_202
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_194 ho hN hs hav hx hvalid
  · exact reject7_195 ho hN hs hav hx hvalid
  · exact reject7_196 ho hN hs hav hx hvalid
  · exact reject7_197 ho hN hs hav hx hvalid
  · exact reject7_198 ho hN hs hav hx hvalid
  · exact reject7_199 ho hN hs hav hx hvalid
  · exact reject7_200 ho hN hs hav hx hvalid
  · exact reject7_201 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_203 : State := ⟨3609300317901135635496057144001, 4210850371101961027017427250403, 0⟩

private noncomputable def tree7_203 : AbundanceTree :=
  .split 200741603328100897 [
    (1, .split 412450637 [
      (2, .split 24302218339165201 [
        (2, .split 1099419593267755489 [
          (2, .split 998772463994140494541 []),
          (4, .round 1 [(4759, 1), (46489, 1), (809359, 1), (4966373, 1), (36094178999551, 1)])]),
        (4, .abundant [(3, 2), (5, 2), (7, 12)]),
        (6, .round 1 [(46455802850145871752614841597004990032610873141502378216730750841499792397297866191, 1)])]),
      (4, .split 766535351221994161 [
        (4, .abundant [(3, 2), (5, 2), (7, 12)])]),
      (6, .split 79306375489603447001962452043975271766853 [
        (2, .round 1 [(3163, 1), (4966373, 1), (23451457, 1)])]),
      (10, .round 1 [(4966373, 1), (68639539, 1), (25858750594965508192854545933664197438924387900541054452875859, 1)]),
      (12, .round 1 [(5262526128099907205596938832298903764707217187257657493982352598814572641014629222714803, 1)])]),
    (2, .split 64175509327 [
      (2, .split 1372831999148013167419 [
        (2, .split 13497507485599466117034304370929 [
          (1, .abundant [(3, 4), (5, 2), (7, 12)]),
          (2, .round 1 [(59954796907, 1)])]),
        (4, .round 1 [(2630809123, 1), (59954796907, 1)])]),
      (4, .split 352207153580443061 [
        (1, .split 739367693312861 [
          (2, .round 1 [(1776701, 1), (4700567, 1), (9382501, 1), (2630809123, 1), (59954796907, 1), (32854413481265798429287897, 1)]),
          (4, .abundant [(3, 4), (5, 2), (7, 12)])]),
        (2, .round 739367693312861 [(433, 1), (601, 1), (1327, 1), (106747, 1), (1776701, 1), (2630809123, 1), (2897011417, 1), (5969148541, 1), (59954796907, 1), (67201361737, 1), (739367693312861, 1)])]),
      (6, .split 2502491576291568125251397593 [
        (1, .round 1 [(148074991, 1), (2630809123, 1), (59954796907, 1), (145132549640036045501933, 1)])])]),
    (4, .split 3552658161374674104981850039367109409269541753023611 []),
    (6, .round 1 [(346380317418392739114048193039441850807465213677477221857651718261029723596828803494870844352931, 1)])]

private theorem checked7_203 : replayAbundance bank 7 2413 (10^300) 7 state7_203 tree7_203 = true := by
  decide +kernel

theorem reject7_203 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_203 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree7_203 checked7_203

@[expose] noncomputable def state7_204 : State := ⟨941173215729536017704649638369044247736025851240801, 1098035418407789954742766228663748887530941553726005, 0⟩

private noncomputable def tree7_204 : AbundanceTree :=
  .split 222942691488419051165955167217344876341 [
    (1, .split 6523322573280182377089727 [
      (2, .abundant [(3, 2), (5, 2), (7, 12)])]),
    (2, .abundant [(3, 2), (5, 1), (7, 12)])]

private theorem checked7_204 : replayAbundance bank 7 2413 (10^300) 5 state7_204 tree7_204 = true := by
  decide +kernel

theorem reject7_204 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_204 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_204 checked7_204

@[expose] noncomputable def state7_205 : State := ⟨245423473799981911005548007565976966340408585303944551655874728855577601, 286327386114754946878915254296226390470465385759234312836155785508075207, 0⟩

private noncomputable def tree7_205 : AbundanceTree :=
  .split 14020072124657538094183043839811142289 [
    (1, .split 62668508098045683783584513 []),
    (2, .round 1 [(445646455759, 1), (29250123049599147533858113260558877253329048079143, 1)])]

private theorem checked7_205 : replayAbundance bank 7 2413 (10^300) 4 state7_205 tree7_205 = true := by
  decide +kernel

theorem reject7_205 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_205 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_205 checked7_205

@[expose] noncomputable def state7_206 : State := ⟨16688187789005224749704673164752914777004924246250130736562207377120194412084476324620672127725041484725022971201, 19469552421510830358003984860492177340134337230343986788280342206796566588702091729486161721917778761608342314411, 0⟩

private noncomputable def tree7_206 : AbundanceTree :=
  .split 42223362249943191270479011547514088211349705097809873373648793992949125900561049993 [
    (1, .round 1 [(54869, 1)])]

private theorem checked7_206 : replayAbundance bank 7 2413 (10^300) 4 state7_206 tree7_206 = true := by
  decide +kernel

theorem reject7_206 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_206 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_206 checked7_206

@[expose] noncomputable def state7_207 : State := ⟨4351667631584058156144901635310935401224795025228179699604091685727665885131353181337409621310629781385425238882837448506877450028001, 5076945570443399191501175352821669327952163336435996290393228211066392613079007871947253553684428324141784159082223940801274303164413, 0⟩

private noncomputable def tree7_207 : AbundanceTree :=
  .split 24184431630358017189722420442790936263972733350624509678066930704096840309459344712976298206511417239870211176890697330401 []

private theorem checked7_207 : replayAbundance bank 7 2413 (10^300) 3 state7_207 tree7_207 = true := by
  decide +kernel

theorem reject7_207 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_207 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_207 checked7_207

@[expose] noncomputable def state7_208 : State := ⟨13841287201, 16148168401, 0⟩

private theorem checked7_208 : checkChildren bank 7 2413 (10^300) state7_208 16148168401 [state7_202, state7_203, state7_204, state7_205, state7_206, state7_207] = true := by
  decide +kernel

theorem reject7_208 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_208 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_202, state7_203, state7_204, state7_205, state7_206, state7_207] ?_ checked7_208
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_202 ho hN hs hav hx hvalid
  · exact reject7_203 ho hN hs hav hx hvalid
  · exact reject7_204 ho hN hs hav hx hvalid
  · exact reject7_205 ho hN hs hav hx hvalid
  · exact reject7_206 ho hN hs hav hx hvalid
  · exact reject7_207 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_209 : State := ⟨91976511762764547686089, 107305930428663263359690, 2767631689⟩

private noncomputable def tree7_209 : AbundanceTree :=
  .split 276763169 [
    (4, .split 9791642389174771 [
      (2, .abundant [(3, 2), (5, 2), (7, 16)]),
      (4, .split 36165903356893317750121 []),
      (6, .round 1 [(14009, 1), (19937, 1), (162079, 1), (280589, 1), (345221, 1), (9327281, 1)])]),
    (6, .split 6497608775732282871610271955234871 [
      (2, .abundant [(3, 2), (5, 2), (7, 16)])]),
    (10, .split 21380277580149775945140880081322841495809555274608732352711935777551 []),
    (12, .round 1 [(24024775850869, 1), (113382239440331993, 1), (1218533342242851172487, 1), (29538118531632786641201299, 1)]),
    (16, .round 1 [(14009, 1)])]

private theorem checked7_209 : replayAbundance bank 7 2413 (10^300) 5 state7_209 tree7_209 = true := by
  decide +kernel

theorem reject7_209 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_209 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_209 checked7_209

@[expose] noncomputable def state7_210 : State := ⟨4170856511095732173812414029996951660667707841040569, 4866346755078044040725969301744362948784036614449710, 14009⟩

private noncomputable def tree7_210 : AbundanceTree :=
  .abundant [(3, 4), (5, 2), (7, 16)]

private theorem checked7_210 : replayAbundance bank 7 2413 (10^300) 3 state7_210 tree7_210 = true := by
  decide +kernel

theorem reject7_210 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_210 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_210 checked7_210

@[expose] noncomputable def state7_211 : State := ⟨58429528863940112022938108146227295814293919145137331121, 68172652039236409978524682158412961973096079194783632961, 0⟩

private noncomputable def tree7_211 : AbundanceTree :=
  .split 125731 [
    (2, .split 4618291 [
      (2, .split 136417 [
        (1, .abundant [(3, 4), (7, 16), (13, 2), (43, 2), (103, 2), (109, 2), (139, 2), (163, 2), (223, 2)]),
        (4, .abundant [(3, 4), (7, 16), (13, 1), (41, 1), (43, 2), (103, 2), (109, 1)]),
        (6, .split 132448720544732470445113 [
          (1, .abundant [(3, 4), (7, 16), (13, 2), (43, 2), (103, 2), (109, 2), (139, 2), (163, 2), (223, 2)]),
          (2, .abundant [(3, 6), (7, 16), (13, 1), (31, 2), (43, 2), (103, 2)])]),
        (10, .abundant [(3, 4), (7, 16), (13, 1), (23, 2), (43, 2)]),
        (12, .split 15451 [
          (2, .abundant [(3, 6), (7, 16), (13, 1), (43, 2), (103, 2), (109, 1), (139, 2), (163, 2), (223, 2)]),
          (4, .abundant [(3, 4), (5, 1), (7, 16)]),
          (6, .abundant [(3, 4), (7, 16), (13, 1), (29, 1), (43, 2), (103, 2)])]),
        (16, .abundant [(3, 4), (7, 16), (13, 1), (43, 2), (103, 2), (109, 1), (139, 2), (163, 2), (223, 2), (239, 2)])]),
      (4, .abundant [(3, 4), (5, 1), (7, 16)]),
      (6, .split 4441 [
        (1, .abundant [(3, 4), (7, 16), (13, 2), (43, 2), (103, 2), (109, 2), (139, 2), (163, 2), (223, 2)]),
        (2, .split 6575641 [
          (1, .abundant [(3, 4), (7, 16), (13, 2), (43, 2), (103, 2), (109, 2), (139, 2), (163, 2), (223, 2)]),
          (4, .abundant [(3, 4), (5, 1), (7, 16)]),
          (6, .abundant [(3, 4), (7, 16), (13, 1), (29, 1), (43, 2), (103, 2)])]),
        (4, .abundant [(3, 4), (5, 1), (7, 16)]),
        (6, .split 24750362743 [
          (2, .abundant [(3, 4), (7, 16), (13, 1), (31, 2), (43, 2), (103, 2)]),
          (4, .abundant [(3, 4), (7, 16), (13, 1), (43, 2), (71, 2), (103, 2), (109, 1), (139, 2)])]),
        (10, .abundant [(3, 4), (7, 16), (13, 1), (23, 2), (43, 2)]),
        (12, .abundant [(3, 4), (7, 16), (13, 1), (43, 2), (53, 1), (103, 2), (109, 1), (139, 2)]),
        (16, .round 1 [(8344043, 1), (17423267, 1)])]),
      (10, .abundant [(3, 4), (7, 16), (13, 1), (23, 2), (43, 2)]),
      (12, .split 72073 [
        (1, .abundant [(3, 4), (7, 16), (13, 2), (43, 2), (103, 2), (109, 2), (139, 2), (163, 2), (223, 2)]),
        (2, .abundant [(3, 4), (7, 16), (13, 1), (43, 2), (103, 2), (109, 1), (139, 2), (163, 2), (193, 1), (223, 2)]),
        (4, .round 1 [(2624711, 1), (87210971, 1)])])]),
    (4, .abundant [(3, 2), (5, 1), (7, 16)]),
    (6, .split 90877849553975005003444747 [
      (2, .abundant [(3, 4), (7, 16), (13, 1), (29, 1), (43, 2), (103, 2)])]),
    (10, .abundant [(3, 2), (7, 16), (11, 2), (13, 1), (23, 2)]),
    (12, .split 4441 [
      (1, .split 2659 [
        (2, .abundant [(3, 4), (7, 16), (13, 2), (43, 2), (53, 2), (103, 2), (109, 2)]),
        (4, .split 1100739151 [
          (2, .abundant [(3, 4), (7, 16), (13, 2), (43, 2), (53, 2), (67, 2), (103, 2)]),
          (4, .abundant [(3, 2), (5, 2), (7, 16)])]),
        (6, .abundant [(3, 2), (7, 16), (13, 2), (29, 2), (43, 2), (53, 2), (71, 2)]),
        (10, .round 1 [(1577535103, 1), (125886075765809280952603, 1)]),
        (12, .abundant [(3, 2), (7, 16), (13, 2), (43, 2), (53, 2), (79, 2), (103, 2), (109, 2), (131, 2), (139, 2), (223, 2)])]),
      (2, .abundant [(3, 4), (7, 16), (13, 1), (43, 2), (53, 1), (103, 2), (109, 1), (139, 2)]),
      (4, .abundant [(3, 2), (5, 1), (7, 16)]),
      (6, .split 24750362743 [
        (2, .abundant [(3, 4), (7, 16), (13, 1), (31, 2), (43, 2), (53, 1)])]),
      (10, .abundant [(3, 2), (7, 16), (13, 1), (23, 2), (43, 2), (53, 1), (103, 2), (109, 1)]),
      (12, .round 1 [(1400803, 1), (60571603, 1)])]),
    (16, .split 4441 [
      (1, .split 2659 [
        (2, .split 54829 [
          (2, .round 1 [(13, 1), (103, 1), (109, 1), (139, 1), (223, 1), (751, 1), (1567, 1), (2221, 1), (1002091357, 1)]),
          (4, .abundant [(3, 4), (7, 16), (11, 2), (13, 2)])]),
        (4, .round 1 [(109, 1), (139, 1), (181, 1), (223, 1), (251, 1), (751, 1), (1567, 1), (2221, 1), (1100739151, 1)]),
        (6, .abundant [(3, 2), (7, 16), (13, 2), (29, 2), (43, 2), (71, 2), (103, 2), (109, 2)])]),
      (2, .split 6575641 [
        (1, .split 3287821 [
          (2, .round 1 [(1567, 1), (2659, 1), (965647, 1), (3731443, 1)])])]),
      (4, .abundant [(3, 2), (5, 1), (7, 16)]),
      (6, .round 1 [(119655719, 1), (24750362743, 1)])]),
    (18, .split 4441 [
      (1, .split 2659 [
        (2, .round 1 [(103, 1), (109, 1), (139, 1), (223, 1), (751, 1), (1567, 1), (2221, 1), (54829, 1)]),
        (4, .round 1 [(1100739151, 1)])]),
      (2, .split 6575641 [
        (1, .round 1 [(223, 1), (751, 1), (1567, 1), (2659, 1), (3287821, 1)])]),
      (4, .abundant [(3, 2), (5, 1), (7, 16)])])]

private theorem checked7_211 : replayAbundance bank 7 2413 (10^300) 7 state7_211 tree7_211 = true := by
  decide +kernel

theorem reject7_211 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_211 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree7_211 checked7_211

@[expose] noncomputable def state7_212 : State := ⟨11466916631397812843874723457900159102557771177878942263282312801, 13379024829993905456009712227492841413895715917865876349950891551, 0⟩

private noncomputable def tree7_212 : AbundanceTree :=
  .split 113990869481 [
    (1, .abundant [(3, 4), (7, 16), (13, 2), (31, 2), (43, 2), (103, 2)]),
    (4, .abundant [(3, 2), (5, 1), (7, 16)]),
    (6, .split 337901 [
      (1, .split 4441 [
        (2, .split 6575641 [
          (4, .abundant [(3, 4), (5, 2), (7, 16)])]),
        (4, .abundant [(3, 4), (5, 2), (7, 16)]),
        (6, .round 1 [(751, 1), (1567, 1), (2591, 1), (2659, 1), (119655719, 1), (24750362743, 1)]),
        (10, .abundant [(3, 4), (7, 16), (13, 2), (23, 2), (43, 2)])]),
      (2, .split 16311060529 [
        (2, .round 26078086201549 [(13, 1), (43, 1), (103, 1), (109, 1), (139, 1), (751, 1), (1567, 1), (2659, 1), (4441, 1), (3400693, 1), (26078086201549, 1)])]),
      (4, .abundant [(3, 2), (5, 1), (7, 16)]),
      (6, .round 8095038006856277 [(666667, 1), (393452473, 1), (8095038006856277, 1)])])]

private theorem checked7_212 : replayAbundance bank 7 2413 (10^300) 7 state7_212 tree7_212 = true := by
  decide +kernel

theorem reject7_212 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_212 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree7_212 checked7_212

@[expose] noncomputable def state7_213 : State := ⟨2250406251565330709458942581912422114108055016380563585248003777689188881, 2625661464636975163064026327611693584120742535167747675515330751303517341, 0⟩

private noncomputable def tree7_213 : AbundanceTree :=
  .split 964845838627086137 [
    (1, .split 2129902711 [
      (2, .split 1512161853485017411 [
        (2, .split 7834583 [
          (2, .split 4721592201421 []),
          (4, .abundant [(3, 6), (7, 16), (11, 2), (13, 2)]),
          (6, .round 1 [(33036751038769505246701838636384321364799, 1)])]),
        (4, .abundant [(3, 4), (5, 2), (7, 16)])]),
      (4, .abundant [(3, 4), (5, 2), (7, 16)]),
      (6, .split 7834583 [
        (2, .round 1 [(103, 1), (109, 1), (139, 1), (353, 1), (751, 1), (1567, 1), (2659, 1), (4441, 1), (213881, 1), (4721592201421, 1)]),
        (4, .abundant [(3, 4), (7, 16), (11, 2), (13, 2)])])]),
    (2, .split 2149948019205554605223968761765979 [
      (2, .round 4441 [(43, 1), (103, 1), (109, 1), (139, 1), (433, 1), (751, 1), (1567, 1), (2659, 1), (4441, 1), (7834583, 1)])]),
    (4, .split 7834583 [
      (2, .split 4721592201421 [
        (1, .round 1 [(2659, 1), (3137, 1), (4441, 1), (5711, 1), (12553, 1), (59951, 1)])]),
      (4, .abundant [(3, 2), (7, 16), (11, 2), (13, 1), (41, 1)])])]

private theorem checked7_213 : replayAbundance bank 7 2413 (10^300) 7 state7_213 tree7_213 = true := by
  decide +kernel

theorem reject7_213 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_213 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree7_213 checked7_213

@[expose] noncomputable def state7_214 : State := ⟨86674125147871622999839571649530459377648640880740409568739928994578294821461618182192241, 101127034384832442875691242257095181803653527082279909142344415621558180226941259474054521, 0⟩

private noncomputable def tree7_214 : AbundanceTree :=
  .split 1563806856705113042288240129 [
    (1, .abundant [(3, 4), (5, 2), (7, 16)])]

private theorem checked7_214 : replayAbundance bank 7 2413 (10^300) 4 state7_214 tree7_214 = true := by
  decide +kernel

theorem reject7_214 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_214 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_214 checked7_214

@[expose] noncomputable def state7_215 : State := ⟨17009977429124238734565978602368955325749510659666978198657523612978228076143366029882664438303521, 19846390943381921750668030606430066444040338097753637148754060825185670633854637385328201868157911, 0⟩

private noncomputable def tree7_215 : AbundanceTree :=
  .split 4441 [
    (1, .split 2659 [
      (2, .split 54829 [
        (2, .split 1002091357 [
          (4, .abundant [(3, 4), (7, 16), (11, 2), (13, 2)])]),
        (4, .abundant [(3, 4), (7, 16), (11, 2), (13, 2)]),
        (6, .split 900005345611 []),
        (10, .split 2221 [
          (2, .round 1 [(103, 1), (109, 1), (139, 1), (751, 1), (1567, 1), (235003, 1)]),
          (4, .abundant [(3, 4), (5, 2), (7, 16)])]),
        (12, .round 1 [(751, 1), (1567, 1), (2221, 1)])]),
      (4, .split 1100739151 [
        (2, .abundant [(3, 4), (7, 16), (13, 2), (43, 2), (67, 2), (103, 2), (109, 2), (139, 2)]),
        (4, .abundant [(3, 2), (5, 2), (7, 16)]),
        (6, .round 1 [(2248692125627750652731854780635410567835399705986327, 1)])]),
      (6, .abundant [(3, 2), (7, 16), (13, 2), (29, 2), (43, 2), (71, 2), (103, 2), (109, 2)]),
      (10, .split 125886075765809280952603 []),
      (12, .round 1 [(139, 1), (751, 1), (1567, 1), (2081, 1), (2221, 1), (131041, 1), (35047559, 1), (1399927283, 1), (902490190057, 1)]),
      (16, .round 1 [(601693206573280339534038151, 1)]),
      (18, .round 1 [(23374892729, 1)])]),
    (2, .split 6575641 [
      (1, .split 3287821 [
        (2, .split 3731443 [
          (2, .split 965647 [
            (2, .split 44403575917 [
              (2, .round 1 [(28429, 1), (32413, 1), (23118148771338961, 1)])]),
            (4, .abundant [(3, 6), (7, 16), (13, 2), (43, 2), (101, 2), (103, 2), (109, 2), (139, 2)]),
            (6, .round 1 [(31594228050636331605145237079, 1)])]),
          (4, .abundant [(3, 4), (7, 16), (13, 2), (31, 2), (43, 2), (103, 2)]),
          (6, .round 1 [(327354367592573467305243197, 1)])]),
        (4, .abundant [(3, 4), (5, 2), (7, 16)]),
        (6, .round 1 [(1709, 1), (2659, 1), (15302827, 1), (1123225451327062737392880023, 1)])]),
      (4, .abundant [(3, 4), (5, 1), (7, 16)]),
      (6, .abundant [(3, 4), (7, 16), (13, 1), (29, 1), (43, 2), (103, 2)])]),
    (4, .abundant [(3, 2), (5, 1), (7, 16)]),
    (6, .split 24750362743 [
      (2, .abundant [(3, 4), (7, 16), (13, 1), (31, 2), (43, 2), (103, 2)]),
      (4, .round 1 [(2591, 1), (2659, 1), (55631, 1), (119655719, 1)])]),
    (10, .abundant [(3, 2), (7, 16), (13, 1), (23, 2), (43, 2), (103, 2), (109, 1), (139, 2), (199, 2)]),
    (12, .split 13090163804301575237372774129 [
      (1, .abundant [(3, 4), (5, 2), (7, 16)])]),
    (16, .round 1881712295828318261112803981300473 [(418813, 1), (8344043, 1), (17423267, 1), (1881712295828318261112803981300473, 1)]),
    (18, .round 166841145079410419543035902775079530383218007133 [(2281485885577, 1), (166841145079410419543035902775079530383218007133, 1)])]

private theorem checked7_215 : replayAbundance bank 7 2413 (10^300) 9 state7_215 tree7_215 = true := by
  decide +kernel

theorem reject7_215 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_215 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 9 h tree7_215 checked7_215

@[expose] noncomputable def state7_216 : State := ⟨655137227524532273713207305665978947782820925692448840201361696275781464898138849921227260117277125985343026705281, 764381351662065924563822438483844280725980722805840171735083290513784798244914472828507138240745778654316630514291, 0⟩

private noncomputable def tree7_216 : AbundanceTree :=
  .abundant [(3, 2), (7, 16), (13, 1), (17, 1), (43, 2), (103, 2), (109, 1)]

private theorem checked7_216 : replayAbundance bank 7 2413 (10^300) 3 state7_216 tree7_216 = true := by
  decide +kernel

theorem reject7_216 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_216 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_216 checked7_216

@[expose] noncomputable def state7_217 : State := ⟨128572044242259937267878530921351459404568942717489450875553691927812062387488202323987535871943940028322744489749969939761, 150011430941273246454839170866948924972421907616530292656407476471657830708076368037656522729070339797237967155374323439281, 0⟩

private noncomputable def tree7_217 : AbundanceTree :=
  .split 4441 [
    (1, .split 2659 [
      (2, .split 54829 [
        (2, .split 1002091357 []),
        (4, .abundant [(3, 4), (7, 16), (11, 2), (13, 2)]),
        (6, .round 1 [(12671, 1), (900005345611, 1)])]),
      (4, .split 1100739151 [
        (2, .abundant [(3, 4), (7, 16), (13, 2), (43, 2), (67, 2), (103, 2), (109, 2), (139, 2)])]),
      (6, .abundant [(3, 2), (7, 16), (13, 2), (29, 2), (43, 2), (71, 2), (103, 2), (109, 2)]),
      (10, .round 1 [(125886075765809280952603, 1)])]),
    (2, .split 6575641 [
      (1, .split 3287821 [
        (2, .split 3731443 [
          (2, .round 1 [(1567, 1), (2659, 1), (3049, 1), (6709, 1), (32413, 1), (965647, 1)])]),
        (4, .abundant [(3, 4), (5, 2), (7, 16)])]),
      (4, .abundant [(3, 4), (5, 1), (7, 16)])]),
    (4, .abundant [(3, 2), (5, 1), (7, 16)]),
    (6, .split 24750362743 [
      (2, .abundant [(3, 4), (7, 16), (13, 1), (31, 2), (43, 2), (103, 2)])]),
    (10, .abundant [(3, 2), (7, 16), (13, 1), (23, 2), (43, 2), (103, 2), (109, 1), (139, 2), (199, 2)])]

private theorem checked7_217 : replayAbundance bank 7 2413 (10^300) 7 state7_217 tree7_217 = true := by
  decide +kernel

theorem reject7_217 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_217 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 7 h tree7_217 checked7_217

@[expose] noncomputable def state7_218 : State := ⟨4951936764937400191766769292182801588680985449148962614257652717575501878148185207481021218326804374850850956128032968435674530871393835921, 5777672155847972395856205429882035197704213866710746988000982173696859764800541081881826389941164166922971745087448770726660103463100462861, 0⟩

private noncomputable def tree7_218 : AbundanceTree :=
  .split 14537 [
    (1, .abundant [(3, 4), (7, 16), (13, 2), (43, 2), (47, 2), (103, 2), (109, 2)]),
    (2, .split 16256839 [
      (2, .abundant [(3, 4), (7, 16), (13, 2), (31, 2), (43, 2), (47, 2)])]),
    (4, .round 44661061166939221 [(103, 1), (109, 1), (139, 1), (751, 1), (1567, 1), (2659, 1), (4441, 1), (44661061166939221, 1)]),
    (6, .round 1 [(9437970569973834539191087, 1)])]

private theorem checked7_218 : replayAbundance bank 7 2413 (10^300) 5 state7_218 tree7_218 = true := by
  decide +kernel

theorem reject7_218 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_218 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_218 checked7_218

@[expose] noncomputable def state7_219 : State := ⟨297726926339905216204755088157395364456257251841, 347348091011994578210276181423580510262957645571, 0⟩

private theorem checked7_219 : checkChildren bank 7 2413 (10^300) state7_219 14009 [state7_210, state7_211, state7_212, state7_213, state7_214, state7_215, state7_216, state7_217, state7_218] = true := by
  decide +kernel

theorem reject7_219 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_219 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_210, state7_211, state7_212, state7_213, state7_214, state7_215, state7_216, state7_217, state7_218] ?_ checked7_219
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_210 ho hN hs hav hx hvalid
  · exact reject7_211 ho hN hs hav hx hvalid
  · exact reject7_212 ho hN hs hav hx hvalid
  · exact reject7_213 ho hN hs hav hx hvalid
  · exact reject7_214 ho hN hs hav hx hvalid
  · exact reject7_215 ho hN hs hav hx hvalid
  · exact reject7_216 ho hN hs hav hx hvalid
  · exact reject7_217 ho hN hs hav hx hvalid
  · exact reject7_218 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_220 : State := ⟨348217824895566037108346013632379081484946870017603667475011761, 406254141070653319526252068991013566990115921961607517860338731, 0⟩

private noncomputable def tree7_220 : AbundanceTree :=
  .split 44126968016931134534995374191 [
    (2, .split 452861683373336082467281481959745577386272566673 [
      (1, .round 1 [(2659, 1), (10567, 1), (14009, 1), (58129, 1), (226430841686668041233640740979872788693136283337, 1)])])]

private theorem checked7_220 : replayAbundance bank 7 2413 (10^300) 5 state7_220 tree7_220 = true := by
  decide +kernel

theorem reject7_220 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_220 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 5 h tree7_220 checked7_220

@[expose] noncomputable def state7_221 : State := ⟨407271371339001520653160951891158322579949176047576965623796533345648009642081, 475149947294096587006813982748815785116026161511480511750516315680978841851091, 0⟩

private noncomputable def tree7_221 : AbundanceTree :=
  .split 91403581555155409 [
    (2, .split 5977948054670257 [
      (1, .split 5434033828476697 [
        (2, .round 1 [(56783, 1), (73417, 1), (11382361, 1), (52638536663, 1), (67095696043, 1), (3791139504307, 1)])]),
      (2, .abundant [(3, 4), (7, 16), (13, 1), (31, 2), (71, 2), (73, 1), (109, 1)]),
      (4, .round 5434033828476697 [(11382361, 1), (5434033828476697, 1)])]),
    (4, .round 1 [(329925711406096959766467384228100449681612400400698891, 1)])]

private theorem checked7_221 : replayAbundance bank 7 2413 (10^300) 6 state7_221 tree7_221 = true := by
  decide +kernel

theorem reject7_221 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_221 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_221 checked7_221

@[expose] noncomputable def state7_222 : State := ⟨557121157805466616391312808972551191395365973334053880432836336599913285475990262841635364936884234851465921, 649974703346754803759179298513314332466156253845874810567267135572146020846506809785476150223624656850229411, 0⟩

private noncomputable def tree7_222 : AbundanceTree :=
  .split 246221854774219414664186198609 [
    (1, .abundant [(3, 2), (5, 2), (7, 16)])]

private theorem checked7_222 : replayAbundance bank 7 2413 (10^300) 4 state7_222 tree7_222 = true := by
  decide +kernel

theorem reject7_222 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_222 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_222 checked7_222

@[expose] noncomputable def state7_223 : State := ⟨651602191844871981954891699066950477925033687414728145046447467860739953985914722392673807311218149956335752365149535235441, 760202579655663802226015269116414715917084848928634202301385627005283527069049490035225119948012463129054120799511690343371, 0⟩

private noncomputable def tree7_223 : AbundanceTree :=
  .split 2559748633561915802707442930459223465566261478367639818017337979434186929768942720172398161 []

private theorem checked7_223 : replayAbundance bank 7 2413 (10^300) 3 state7_223 tree7_223 = true := by
  decide +kernel

theorem reject7_223 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_223 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_223 checked7_223

@[expose] noncomputable def state7_224 : State := ⟨891350075394879216317099743342142095733710008927363800413991067849802781755741416258720051075832438163700498331129822691508284771450379394886529752329681, 1039908452077117230300369638177578332965529827933307562862519130019967073130812256601733305352714602851613754365591897319820621693417683789979772170740891, 0⟩

private noncomputable def tree7_224 : AbundanceTree :=
  .round 1 [(742915421345899, 1)]

private theorem checked7_224 : replayAbundance bank 7 2413 (10^300) 3 state7_224 tree7_224 = true := by
  decide +kernel

theorem reject7_224 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_224 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree7_224 checked7_224

@[expose] noncomputable def state7_225 : State := ⟨254557108598308412421771540874321, 296983293471997801623202401547611, 0⟩

private theorem checked7_225 : checkChildren bank 7 2413 (10^300) state7_225 34199239 [state7_219, state7_220, state7_221, state7_222, state7_223, state7_224] = true := by
  decide +kernel

theorem reject7_225 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_225 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state7_219, state7_220, state7_221, state7_222, state7_223, state7_224] ?_ checked7_225
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject7_219 ho hN hs hav hx hvalid
  · exact reject7_220 ho hN hs hav hx hvalid
  · exact reject7_221 ho hN hs hav hx hvalid
  · exact reject7_222 ho hN hs hav hx hvalid
  · exact reject7_223 ho hN hs hav hx hvalid
  · exact reject7_224 ho hN hs hav hx hvalid

@[expose] noncomputable def state7_226 : State := ⟨1949852764330226021570375035409016471789644172817441, 2274828225873860953897327388755476392410261125299221, 0⟩

private noncomputable def tree7_226 : AbundanceTree :=
  .split 3154908181130328094651 [
    (2, .split 169733293139449312598615732043876613 [
      (1, .split 3683456379316422430481 [
        (2, .round 1 [(323352761, 1), (23039948849747, 1), (158555749118582268157328844678301, 1)])]),
      (2, .round 645053789743325031032852254296596920561 [(323352761, 1), (140392204717, 1), (106041019574217229753, 1), (645053789743325031032852254296596920561, 1)])]),
    (4, .round 3789476976101827007349960603963148366181 [(14009, 1), (5228501, 1), (323352761, 1), (1599246406441, 1), (164771988343271, 1), (186139085244311, 1), (3789476976101827007349960603963148366181, 1)])]

private theorem checked7_226 : replayAbundance bank 7 2413 (10^300) 6 state7_226 tree7_226 = true := by
  decide +kernel

theorem reject7_226 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_226 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_226 checked7_226

@[expose] noncomputable def state7_227 : State := ⟨876297526743081300329904808555552589221245081011720113407104741383423506288414271498586901934250889898957201, 1022347114902984663338089539212077722911049782585774083954927165933752847154876147203136557483258453309205251, 0⟩

private noncomputable def tree7_227 : AbundanceTree :=
  .split 984331538658590182595687175851440780465402860917582854620213137 [
    (1, .split 14009 [
      (2, .split 125731 [
        (2, .round 1 [(4618291, 1)])]),
      (4, .round 1 [(113990869481, 1)])])]

private theorem checked7_227 : replayAbundance bank 7 2413 (10^300) 6 state7_227 tree7_227 = true := by
  decide +kernel

theorem reject7_227 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_227 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 6 h tree7_227 checked7_227

@[expose] noncomputable def state7_228 : State := ⟨6712250796311455265179346099962920601704794326380231516893129967869802697568803613777468454355950198773099639410797631847533921, 7830959265192811085757124575887545981853242195339117240722633990770161621297193412699183677009359030399279264658957865765337661, 0⟩

private noncomputable def tree7_228 : AbundanceTree :=
  .split 4361656956697 [
    (1, .split 8682437 []),
    (2, .round 171387850521690967478437 [(1301, 1), (14009, 1), (885041, 1), (961273, 1), (171387850521690967478437, 1)])]

private theorem checked7_228 : replayAbundance bank 7 2413 (10^300) 4 state7_228 tree7_228 = true := by
  decide +kernel

theorem reject7_228 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 7 ∣ N)
    (hav : Nat.Coprime 2413 N) (hx : N ≤ 10^300) (h : Valid state7_228 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 4 h tree7_228 checked7_228

end OddPerfect.IndexComponent.Size300
