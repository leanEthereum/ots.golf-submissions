import Submissions.UpperCompressions.ProofBundle00

/-!
# Exact finite certificate for the chain-18 compact schedule

This file contains the 160 class populations, alias multiplicities, and upward-rounded
winner-kernel numerators emitted by the independent exact checker.  All finite arithmetic is
replayed by `decide +kernel`; no native evaluator or additional axiom is used.

The per-tier kernel witnesses are scaled by `2^80`.  A `2^512` fixed-point interval calculation,
replayed by the kernel with twenty outward-rounded squarings, proves that every true winner kernel
lies below its emitted witness.  The file also supplies the concrete class/alias decoder and exact
fibers, the resulting unconditional moment bounds, the telescoping winner-mass identity, and the
collision-aware availability theorem.
-/

namespace OptimalOTS.Chain18Compact

open scoped BigOperators
open WeightedReplacement
noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev Tier := Fin 160

def classCounts : List ℕ := [
  165731999761240428825280379636982,
  125101092296928349909349745170056,
  94431256216089188254454238970816,
  71280439214679869396883673157760,
  53805280705275528801579406248727,
  40614337213475518115423997406535,
  30657290823430432966450483090124,
  23141319132929456209990422805230,
  17467967848155829614895249449205,
  13185499623199887973735927456093,
  9952925010731272164895729703264,
  7512851553162152133073691073786,
  5670989169828161664594803168375,
  4280679990086918253970188541099,
  3231220844210418013302776126230,
  2439048607457098614663207699439,
  1841086542456224531384660062387,
  1389721850986611658646721852121,
  1049014528746915864863585608976,
  791835657409419951977414052243,
  597707273409637493846164093330,
  451171815063272483817181820070,
  340561316636254562544048189033,
  257068347395883153427869118686,
  194044719802390705467326205119,
  146472126901480057725075844286,
  110562558692333931513121563697,
  83456680795443325980077728971,
  62996158924854507385146779933,
  47551800559238723660219735465,
  35893829621573386919327638513,
  27093964799712813996107866717,
  20451504493937628111611385495,
  15437532898934671245268355819,
  11652804619783219222825092805,
  8795954373550464257418133187,
  6639500462990419782150293945,
  5011731288576261761358646194,
  3783032603006469023783426663,
  2855566807568514869401664626,
  2155482497213393642552334799,
  1627033933323416464178306653,
  1228142202124393394333938413,
  927044611773530734729946162,
  699765532902254255882669585,
  528207295459998437631714284,
  398709127218141171227199229,
  300959387550896932311484067,
  227174481609254361124026100,
  171479074727162212093138654,
  129438255671523175449905786,
  97704396469499522435865907,
  73750589418852839617655009,
  55669435721382332145080314,
  42021163903352732757424743,
  31718984151449700456075808,
  23942549666433556419747142,
  18072634208566652132655347,
  13641824388194098933253954,
  10297300460537068758681034,
  7772741955795639434336362,
  5867121060242115960443165,
  4428695116524665571455995,
  3342923603314350113026246,
  2523347450526688545220041,
  1904704429692100936124696,
  1437732412291082072409861,
  1085246689847959680306052,
  819179000244386363304360,
  618342483295910242350433,
  466744592871478778025344,
  352313625522030850971949,
  265937461077325695922934,
  200737971540001130539217,
  151523320462987011209033,
  114374540121877432499365,
  86333466124521523624208,
  65167180042901882273250,
  49190202879601920531609,
  37130280804636090719557,
  28027075797675732155797,
  21155694010969748663664,
  15968962469901098818403,
  12053857640189544715046,
  9098616291479564328081,
  6867909709862722723408,
  5184104390673977225809,
  3913117005557457768473,
  2953737277408126122648,
  2229568544749364557121,
  1682944242771073200267,
  1270335869952951628630,
  958886775912744390017,
  723795755147298896171,
  546342101362995046627,
  412394856643032957910,
  311287546208925242061,
  234968793239451965363,
  177361176629497357076,
  133877277042473824608,
  101054373592278744641,
  76278701709758331822,
  57577314565862195826,
  43460973746061021848,
  32805558372890843224,
  24762549133291848982,
  18691458931586911737,
  14108829522906049070,
  10649732650548363701,
  8038709960338758094,
  6067837587675360919,
  4580168660944568731,
  3457235216694151008,
  2609614279476941117,
  1969806863928418164,
  1486862838776637052,
  1122323618742020451,
  847159591503579904,
  639458399697641405,
  482679990102924771,
  364339475094505175,
  275012919126245256,
  207586878293404518,
  156691931688675222,
  118275095002969961,
  89277066383331215,
  67388602639681841,
  50866625265039123,
  38395412192495017,
  28981821524425273,
  21876203540123108,
  16512702926967615,
  12464197286774940,
  9408283504414587,
  7101603344862421,
  5360463726884979,
  4046208389279397,
  3054176036472545,
  2305365655144756,
  1740145276003139,
  1313503182415911,
  991463398871256,
  748380008613016,
  564894834661441,
  426395844894780,
  321853516712208,
  242942495403862,
  183378599587223,
  138418376152413,
  104481351742480,
  78864898708657,
  59529008823677,
  44933835138503,
  33917064561959,
  25601355668062,
  19324470487167,
  14586536279567,
  11010237443246,
  8310767404981,
  6273147585895
]

def aliasCounts : List ℕ := [
  374796160129614344588800418032272040264,
  496524178811188706349674565461928778721,
  657787681855828200261444048859144689780,
  871427249964568622755447793049363795441,
  1154453918033824497680376761175876143849,
  1529403688028314468790370394278474674308,
  2026131972289016638385179509889204793166,
  2684190852055885135989575102515422821517,
  3555978443575673527623646507177704475658,
  4710911144528984194092749337429760923087,
  6240950982162703981950181663046945291152,
  8267928186997203123799178692869558031342,
  10953242064293566790664703598699655617430,
  14510712612239399909637664973644470601946,
  19223606220667868734955765612371825046945,
  25467191154454125354316370488689562310994,
  33738618847458116128940539481011177221413,
  44696510367896263455253488554151627765792,
  59213400214117574217686668237122196520431,
  78445213397352777439915958704490975819481,
  103923308088212255381832604619631564085470,
  137676412947923055602792252494905571217339,
  182392168713217048323904929313836475396289,
  241631137206703155574268515730465487487169,
  320110318819145650350050579656579582647307,
  424078754334572396043491723890759072889851,
  561815119474274497500087090242174519157651,
  744286934599806742196381821383497108606417,
  986023881157743670793023093755932065302436,
  1306274765426243412875800827357729103012296,
  1730540256528700396832179802710939217757896,
  2292603448048086255344476517688880506855536,
  3037219933600866910853831445718594085232562,
  4023681602997692578097822903465568929547919,
  5330537938966201618514927435798645712862723,
  7061850764926401653766276903357027004540367,
  9355480501486140438304494962414444412530347,
  12394063756510971399110341003532922757234588,
  16419556382292393261238419787216819495921515,
  21752500048845277939415348504158986039519184,
  28817546512865788706569598505229243251578010,
  38177272058632544663551650024892317930417060,
  50576974729530247447001018029816470918672246,
  67004021524143679087176976863538127276446481,
  88766471340039005437432139511231773717923738,
  117597234371820877646274592795360128479132234,
  155792062134385027973080377947619308460968423,
  206392356213212775438417597512118089335114413,
  273427352760314073159889546581473133286696298,
  362234967852179406835583092357948273059075478,
  479886852606750075298582278874156196180050029,
  635751505209960522175004505585434916560458607,
  842240280526306589200242802683601219638822411,
  1115795702187381069082564882145179693465739070,
  1478200776731913937317500528894978014114238178,
  1958313570968385064435945712208720841247842838,
  2594365177748746051569802714302143632702643246,
  3437004058416202323175254677962203076713972705,
  4553329184831849028005743370806353454273514552,
  6032233142964476547938495235137200673115755744,
  7991480673663601241244232961308070835377847132,
  10587086321097961376304970171918840875729994472,
  14025737940131494993493176321112602273202370742,
  18581255359688832938137916175819067918828643699,
  24616394824323499686231363805212440459465438081,
  32611735528517774764398704078380475094807676204,
  43203948516491523052930596738117282683431062148,
  57236495353712923223615162483981003761036654004,
  75826793780826949560214363979002758604317791822,
  100455198856827296221579679949574709164988666612,
  133082885307723423655331794194906154227952881447,
  176308018258098446469277903539824947881533009937,
  233572648507213906552750145062413039708618454825,
  309436807817584486967693614510500105798850975820,
  409941630973485953134753067190364737446975192103,
  543090420778300904969355060729389286847719585487,
  719485964243849373463544723496820171828728879387,
  953174850902280547473138183558918721882485954406,
  1262766028291236747104003665188874190711328965756,
  1672912667909565046774112377835594985768601484256,
  2216275346365827133787919499019995485488774873467,
  2936122874953028915196235682046174950186496339595,
  3889777888713378491411561308738908809140739783624,
  5153181576826579789717253682223883442342791807427,
  6826941056881757525928039018950335918059555466870,
  9044340963293860277455984455156291813308670221493,
  11981957236983707380276818246208660954068279228374,
  15873718325543947411760591524260212005805690270331,
  21029533532386798023690202339583581570670327221582,
  27859971951702328351436368970136758618774764052454,
  36908957256265158128041247160210823949601947097842,
  48897081937405736765358902254880276077446446012198,
  64778990263984414773574456998838354140324096890521,
  85819399574226531985630735314147285827995795066461,
  113693813759091545573988106455119996126822849540196,
  150621949135709385783434768192214956730412790814814,
  199544497933191299449802261979103254485775336422807,
  264357305771299585566273791932793314834766534728214,
  350221611637551924949891973933573420539176109971897,
  463975056061293201633302326702219727070424243971340,
  614676187808868332801003259525012492583932569668010,
  814325830524310201014221609140693248965226000208857,
  1078822754924796614828415490122281279241228287059028,
  1429229761027726142233276517440876477408291850473678,
  1893450994342621338834458421953262028420297251291022,
  2508454068551609658732958899168543352224099985827740,
  3323213952879034406145571972222394947035952117293213,
  4402613060159852615319247901466432982663469134046704,
  5832608118844812833154118037944599614092830928688746,
  7727075292874164698498993854156622072368956259596091,
  10236878661235249424379406190927458701982710595946590,
  13561884227273181313892588902282212835002147708705467,
  17966876196671065282930513961857435739911359325450879,
  23802643022617602306640853283169119258697995386920492,
  31533912414761658295157933698653851312894955043156713,
  41776359931237991615353834165800913889432671238460689,
  55345638355841388480188320509849314177409605846476367,
  73322332349290986190818860087078140425632906696909179,
  97138011089518233932080578187851528918419736298575076,
  128689231778325354601840326703008793191504822272229445,
  170488572793280282570488994727018577357858389810980636,
  225864724168106168724898529056517598350703219426734543,
  299227569833775105898180508760474830312723744082210146,
  396419371767847287743170638517865419674273220164924775,
  525180023060267336081570749300662756837322642501992050,
  695763420970927030392899163192048285650077625452231573,
  921754045758149859632661021767168325276975965156105460,
  1221148774809865481713826379066591278465694740029183370,
  1617790084130326413473937708580352277557121231442618954,
  2143264772670180406126671761524664649370956565142000706,
  2839419417870598165097232824593861816550362906754230945,
  3761692885522162976838397403362802020811034547898243331,
  4983531285004817305241037215556934477443916314594756847,
  6602236964050767030404092232982001313367806839319524407,
  8746717340394972272544884390579502539314453661504777020,
  11587750665969184862700451283659231387082893920477253616,
  15351586261768755118888514045473977418837457677131653496,
  20337962311057983720828954812457349338002376561966825007,
  26943976103094488011765429486222701865206856878560375370,
  35695707696190662911327215113282629710635370293573003136,
  47290115435324917915647181755573770708168363006317001043,
  62650539789801111136741979733617920988815933455671213873,
  83000235717460001401237782051377365053894964459893754221,
  109959789521430038331822657058064225393353343077533703199,
  145676178285562612755102482001402035773232037365638386950,
  192993749938289881633181359256266131822755018579050640927,
  255680740489041815724858662451047767239135859606618399404,
  338729367881174610193339979868259033181299997322538987599,
  448753401446634671629342570479588923060001760309551895786,
  594514868779785153383955784377000813167360527229702789151,
  787621846197801960333696988440871657939850429386885065881,
  1043452903862381120012251992711881650557916880841356811047,
  1382381827183258314732093897508503958886208064188534174351,
  1831400149846203588833340061017612896053244918143504934314,
  2426266715188257801386485967271444843632846606067792491983,
  3214355454777656010708001667932325207908569093400212242404,
  4258428178602451156296555971077297989453631330423489774677,
  5641632838646787066261972634025853115662877251818084264408,
  7474125323719979920201302081679068939315584546717376829637,
  9901842140742959321105762597502091375939212910554127043776
]

/-- Upward-rounded true winner multipliers, with common denominator `2^80`. -/
def kernelNumerators : List ℕ := [
  969538078991402286335657307296,
  552426282755565082524494870657,
  314762991166390654864553414445,
  179346482607253888963581865138,
  102188478380472395688330201017,
  58225184073267411252326329543,
  33175668050944403387453441690,
  18902896333099076690379248866,
  10770525597550197077363969017,
  6136847211079531366660992132,
  3496661512645178004905208756,
  1992332157550178211110859704,
  1135193158927080845864811574,
  646811383500611686155951348,
  368540663140274097095691168,
  209987305214151492452724422,
  119646648132859232721588877,
  68172292963762693968163722,
  38843212058787655212854195,
  22132080382872957173822617,
  12610410115531331460207478,
  7185153521273606558505982,
  4093952145310969692394013,
  2332648712503802720078068,
  1329094278800802129969669,
  757289796540054703128379,
  431487571677370888508471,
  245852339726668026294665,
  140081334150353477434463,
  79815283750564347254290,
  45476991181453003840741,
  25911780371518455203268,
  14763952978686311451111,
  8412167695771788135483,
  4793062135195060489324,
  2730977142899395098468,
  1556047823724003772498,
  886599913648033950102,
  505163888728013136973,
  287830478595844264748,
  163998973912236546980,
  93442693975304399328,
  53241396663813868894,
  30335656462070951434,
  17284516052392077149,
  9848292071279647124,
  5611312874459638630,
  3197186115685294015,
  1821676353181178659,
  1037945122448206665,
  591394706437869020,
  336961546132939633,
  191991994640757503,
  109392051721685340,
  62328730899212206,
  35513270498565557,
  20234520785583449,
  11529090453236316,
  6568966370717764,
  3742819638114609,
  2132556908577501,
  1215072601850907,
  692314927821899,
  394461873238974,
  224753383512143,
  128058176426008,
  72963936491679,
  41572780203501,
  23686983123475,
  13496162571521,
  7689723433372,
  4381380879500,
  2496382709290,
  1422365441860,
  810421748294,
  461754196623,
  263093721515,
  149902883220,
  85410124906,
  48664088898,
  27727307930,
  15798166378,
  9001306085,
  5128663976,
  2922152185,
  1664950337,
  948636009,
  540502613,
  307961097,
  175466328,
  99975040,
  56962528,
  32455387,
  18492014,
  10536139,
  6003142,
  3420390,
  1948824,
  1110374,
  632654,
  360465,
  205381,
  117019,
  66674,
  37989,
  21645,
  12333,
  7027,
  4004,
  2281,
  1300,
  741,
  422,
  241,
  137,
  79,
  45,
  26,
  15,
  9,
  5,
  3,
  2,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1,
  1
]

@[simp] theorem classCounts_length : classCounts.length = 160 := by decide +kernel
@[simp] theorem aliasCounts_length : aliasCounts.length = 160 := by decide +kernel
@[simp] theorem kernelNumerators_length : kernelNumerators.length = 160 := by decide +kernel

def classes (i : Tier) : ℕ := classCounts.getD i.val 0
def aliases (i : Tier) : ℕ := aliasCounts.getD i.val 0
def kernelNumerator (i : Tier) : ℕ := kernelNumerators.getD i.val 0

def familyCardinality : ℕ := ∑ i : Tier, classes i
def acceptedAliases : ℕ := ∑ i : Tier, classes i * aliases i

def R : ℕ := 2^256
def L : ℕ := 2^20
def KQ : ℕ := 2^80
def kappa : ℝ := ((2:ℝ)^127)⁻¹

theorem familyCardinality_exact :
    familyCardinality = 676013856769711926075368867014708 := by
  decide +kernel

theorem acceptedAliases_exact :
    acceptedAliases =
      9938514739378411853906048441678916651529596919925356639434040636883783447 := by
  decide +kernel

theorem acceptedAliases_bounds : 90 * 2^236 ≤ acceptedAliases ∧ acceptedAliases < R := by
  rw [acceptedAliases_exact]
  norm_num [R]

theorem keygen_compressions : 7*(8*18+11)+2 = 1087 := rfl

theorem signature_bits : 42*129+86 = 5504 := rfl

/-- Every alias multiplicity is nonzero and fits in a 256-bit oracle-answer fiber. -/
theorem aliases_valid (i : Tier) : 0 < aliases i ∧ aliases i < R := by
  revert i
  decide +kernel

/-- The emitted aliases are strictly increasing with the tier number. -/
theorem aliases_strict {i j : Tier} (h : i < j) : aliases i < aliases j := by
  revert i j
  decide +kernel

/-! ## Concrete class and alias fibers -/

abbrev Class := (j : Tier) × Fin (classes j)
abbrev multiplicity (c : Class) : ℕ := aliases c.1
abbrev Alias := (c : Class) × Fin (multiplicity c)
abbrev M := familyCardinality
abbrev A := acceptedAliases

theorem card_class : Fintype.card Class = M := by
  simp only [Class, Fintype.card_sigma, Fintype.card_fin]
  rfl

theorem card_alias : Fintype.card Alias = A := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  change (∑ c : Class, aliases c.1) = acceptedAliases
  rw [Fintype.sum_sigma]
  have hsum (j : Tier) : (∑ _k : Fin (classes j), aliases j) = classes j * aliases j := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp only [hsum]
  rfl

def classEquiv : Class ≃ Fin M := Fintype.equivFinOfCardEq card_class
def aliasEquiv : Alias ≃ Fin A := Fintype.equivFinOfCardEq card_alias

def classTier (i : Fin M) : Tier := (classEquiv.symm i).1

theorem aliases_lt : A < 2^256 := acceptedAliases_bounds.2

/-- The accepted prefix of 256-bit oracle outputs is in fixed bijection with aliases. -/
def rawAlias (x : BitVec 256) : Option Alias :=
  if h : x.toNat < A then some (aliasEquiv.symm ⟨x.toNat, h⟩) else none

def rawClass (x : BitVec 256) : Option Class := (rawAlias x).map Sigma.fst
def decode (x : BitVec 256) : Option (Fin M) := (rawClass x).map classEquiv
def aliasRaw (a : Alias) : BitVec 256 := BitVec.ofNat 256 (aliasEquiv a).val

theorem aliasRaw_toNat (a : Alias) : (aliasRaw a).toNat = (aliasEquiv a).val := by
  rw [aliasRaw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_trans (aliasEquiv a).isLt aliases_lt

@[simp] theorem rawAlias_aliasRaw (a : Alias) : rawAlias (aliasRaw a) = some a := by
  simp only [rawAlias, aliasRaw_toNat, dif_pos (aliasEquiv a).isLt]
  rw [Equiv.symm_apply_apply]

theorem aliasRaw_of_rawAlias {x : BitVec 256} {a : Alias} (h : rawAlias x = some a) :
    aliasRaw a = x := by
  unfold rawAlias at h
  split_ifs at h with hx
  · simp only [Option.some.injEq] at h
    rw [← h]
    apply BitVec.eq_of_toNat_eq
    rw [aliasRaw_toNat, Equiv.apply_symm_apply]

def aliasFiberEquiv (c : Class) : {a : Alias // a.1 = c} ≃ Fin (multiplicity c) where
  toFun a := a.property ▸ a.val.2
  invFun b := ⟨⟨c,b⟩,rfl⟩
  left_inv := by rintro ⟨⟨d,b⟩,h⟩; cases h; rfl
  right_inv _ := rfl

def rawFiberEquiv (c : Class) :
    {x : BitVec 256 // rawClass x = some c} ≃ {a : Alias // a.1 = c} :=
  (Equiv.ofBijective
    (fun a : {a : Alias // a.1 = c} =>
      (⟨aliasRaw a.val, by simp [rawClass,a.property]⟩ :
        {x : BitVec 256 // rawClass x = some c}))
    (by
      constructor
      · intro a b h
        apply Subtype.ext
        have he := congrArg
          (fun x : {x : BitVec 256 // rawClass x = some c} => rawAlias x.val) h
        simpa using he
      · intro x
        have hx := x.property
        rw [rawClass, Option.map_eq_some_iff] at hx
        obtain ⟨a,ha,hc⟩ := hx
        exact ⟨⟨a,hc⟩,Subtype.ext (aliasRaw_of_rawAlias ha)⟩)).symm

theorem rawClass_fiber (c : Class) :
    (Finset.univ.filter fun x : BitVec 256 => rawClass x = some c).card = multiplicity c := by
  rw [← Fintype.card_subtype, Fintype.card_congr (rawFiberEquiv c),
    Fintype.card_congr (aliasFiberEquiv c), Fintype.card_fin]

theorem decode_eq_some (x : BitVec 256) (i : Fin M) :
    decode x = some i ↔ rawClass x = some (classEquiv.symm i) := by
  rw [decode, Option.map_eq_some_iff]
  constructor
  · rintro ⟨c,hc,hi⟩
    have he : c = classEquiv.symm i := by
      apply classEquiv.injective
      simpa using hi
    simpa [he] using hc
  · intro h
    exact ⟨classEquiv.symm i,h,classEquiv.apply_symm_apply i⟩

theorem decode_fiber (i : Fin M) :
    (Finset.univ.filter fun x : BitVec 256 => decode x = some i).card =
      aliases (classTier i) := by
  have he : (Finset.univ.filter fun x : BitVec 256 => decode x = some i) =
      Finset.univ.filter fun x : BitVec 256 => rawClass x = some (classEquiv.symm i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decode_eq_some]
  rw [he, rawClass_fiber]
  rfl

def acceptedEquiv : {x : BitVec 256 // (rawAlias x).isSome} ≃ Alias :=
  (Equiv.ofBijective
    (fun a : Alias => (⟨aliasRaw a, by simp⟩ : {x : BitVec 256 // (rawAlias x).isSome}))
    (by
      constructor
      · intro a b h
        have he := congrArg
          (fun x : {x : BitVec 256 // (rawAlias x).isSome} => rawAlias x.val) h
        simpa using he
      · intro x
        obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp x.property
        exact ⟨a,Subtype.ext (aliasRaw_of_rawAlias ha)⟩)).symm

theorem rawAlias_accepted_count :
    (Finset.univ.filter fun x : BitVec 256 => (rawAlias x).isSome).card = A := by
  rw [← Fintype.card_subtype, Fintype.card_congr acceptedEquiv, card_alias]

theorem decode_isSome (x : BitVec 256) : (decode x).isSome = (rawAlias x).isSome := by
  simp [decode,rawClass]

theorem accepted_decode_count :
    (Finset.univ.filter fun x : BitVec 256 => (decode x).isSome).card = A := by
  simp only [decode_isSome]
  exact rawAlias_accepted_count

/-! ## Exact integer moment numerators -/

def wMax : ℕ := (kernelNumerators.foldl max 0)
def gMax : ℕ := (List.zipWith (fun a k => a*k) aliasCounts kernelNumerators).foldl max 0
def diagonalMax : ℕ :=
  (List.zipWith (fun a k => a*k^2) aliasCounts kernelNumerators).foldl max 0

def sumGProxyNumerator : ℕ :=
  ∑ i : Tier, classes i * aliases i * kernelNumerator i

def cNumerator : ℕ :=
  ∑ i : Tier, classes i * aliases i^2 * kernelNumerator i^2

def aNumerator : ℕ :=
  ∑ i : Tier, classes i * aliases i^3 * kernelNumerator i^2

def hNumerator : ℕ :=
  ∑ i : Tier, classes i * aliases i^2 * kernelNumerator i

def remainingAliases : ℕ := R - acceptedAliases

def positiveFactor (i : Tier) : ℕ := aliases i * 2^128 - remainingAliases

def positiveNumerator : ℕ :=
  ∑ i : Tier, classes i * aliases i * kernelNumerator i * positiveFactor i

def positiveDenominator : ℕ := 2 * R * KQ * remainingAliases

theorem wMax_exact : wMax = 969538078991402286335657307296 := by
  decide +kernel

theorem gMax_exact :
    gMax = 363379149105420292596180045042320825577259911759085239367962332966144 := by
  decide +kernel

theorem diagonalMax_exact :
    diagonalMax =
      352309922169199529095717430799163996063279887590569250824906269449627463006150171818954067772186624 := by
  decide +kernel

theorem sumGProxyNumerator_exact :
    sumGProxyNumerator =
      139984046386112763159845082994843193628787476910003432326912310728099042595194327348412821162151774316 := by
  decide +kernel

theorem cNumerator_exact :
    cNumerator =
      38399330040078950555363360883962320251036151666450700371140276166266466981281695153859120172186420224993599411375687791846725699684668926874976038236085446572200254553248 := by
  decide +kernel

theorem aNumerator_exact :
    aNumerator =
      19064862593535788205756860300320804708905103192157442540015517667486456977190296769166954021874162667206510054362907344824376199816372983155790320085192813934532844249801111550956857657894156296302857200960040 := by
  decide +kernel

theorem hNumerator_exact :
    hNumerator =
      92068429394040342173498364628350780518845100581885326929342218253508123184818195135114323119447366727595444285033363068624047218964527530102 := by
  decide +kernel

theorem positiveNumerator_exact :
    positiveNumerator =
      15121609115464259302695737513576530143549576171139641167791676197282761718227318305210619020625499581971770488628180815953353537962742551862056274865950059617785527076079289111988 := by
  decide +kernel

theorem positiveDenominator_exact :
    positiveDenominator =
      32415307914866185062370005781725725461396840961716649648017039677216072025904210795108902095020631354953173482015354366010750933758636108712074751479431822811537252724381012983808 := by
  decide +kernel

/-! These are the exact integer comparisons checked by the independent certificate. -/

theorem w_envelope_integer : 5*wMax < 4*L*KQ := by
  rw [wMax_exact]
  norm_num [L,KQ]

theorem g_envelope_integer : 40*gMax*2^127 < 17*L*R*KQ := by
  rw [gMax_exact]
  norm_num [L,R,KQ]

theorem diagonal_envelope_integer :
    40*diagonalMax*2^127 < 13*L^2*R*KQ^2 := by
  rw [diagonalMax_exact]
  norm_num [L,R,KQ]

theorem c_envelope_integer : 25*cNumerator*2^127 < 8*L*R^2*KQ^2 := by
  rw [cNumerator_exact]
  norm_num [L,R,KQ]

theorem a_envelope_integer : 4*aNumerator*2^254 < L*R^3*KQ^2 := by
  rw [aNumerator_exact]
  norm_num [L,R,KQ]

theorem h_envelope_integer : 1000*hNumerator*2^127 < 967*R^2*KQ := by
  rw [hNumerator_exact]
  norm_num [R,KQ]

theorem positive_envelope_integer : 100*positiveNumerator < 47*positiveDenominator := by
  rw [positiveNumerator_exact, positiveDenominator_exact]
  norm_num

/-! Real-number forms used by the security proof. -/

def wRatio : ℝ := (wMax:ℝ) / (L*KQ:ℕ)
def gRatio : ℝ := (gMax:ℝ) * 2^127 / (L*R*KQ:ℕ)
def diagonalRatio : ℝ := (diagonalMax:ℝ) * 2^127 / (L^2*R*KQ^2:ℕ)
def cRatio : ℝ := (cNumerator:ℝ) * 2^127 / (L*R^2*KQ^2:ℕ)
def aRatio : ℝ := (aNumerator:ℝ) * 2^254 / (L*R^3*KQ^2:ℕ)
def hRatio : ℝ := (hNumerator:ℝ) * 2^127 / (R^2*KQ:ℕ)
def positiveRatio : ℝ := (positiveNumerator:ℝ) / positiveDenominator

theorem wRatio_lt : wRatio < 4/5 := by
  unfold wRatio
  rw [wMax_exact]
  norm_num [L,KQ]

theorem gRatio_lt : gRatio < 17/40 := by
  unfold gRatio
  rw [gMax_exact]
  norm_num [L,R,KQ]

theorem diagonalRatio_lt : diagonalRatio < 13/40 := by
  unfold diagonalRatio
  rw [diagonalMax_exact]
  norm_num [L,R,KQ]

theorem cRatio_lt : cRatio < 8/25 := by
  unfold cRatio
  rw [cNumerator_exact]
  norm_num [L,R,KQ]

theorem aRatio_lt : aRatio < 1/4 := by
  unfold aRatio
  rw [aNumerator_exact]
  norm_num [L,R,KQ]

/-- The finite schedule certificate's `H / κ` bound. -/
theorem hRatio_lt : hRatio < 967/1000 := by
  unfold hRatio
  rw [hNumerator_exact]
  norm_num [R,KQ]

theorem positiveRatio_lt : positiveRatio < 47/100 := by
  unfold positiveRatio
  rw [positiveNumerator_exact, positiveDenominator_exact]
  norm_num

theorem moment_envelopes :
    wRatio < 4/5 ∧ gRatio < 17/40 ∧ diagonalRatio < 13/40 ∧
      cRatio < 8/25 ∧ aRatio < 1/4 ∧ hRatio < 967/1000 ∧
      positiveRatio < 47/100 :=
  ⟨wRatio_lt, gRatio_lt, diagonalRatio_lt, cRatio_lt, aRatio_lt,
    hRatio_lt, positiveRatio_lt⟩

def probability (i : Tier) : ℝ := (aliases i : ℝ)/(R:ℝ)
def kernelUpper (i : Tier) : ℝ := (kernelNumerator i : ℝ)/(KQ:ℝ)
def winner (w : Tier → ℝ) (i : Tier) : ℝ := probability i * w i

structure KernelBounds (w : Tier → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ w i
  upper : ∀ i, w i ≤ kernelUpper i

def hValue (w : Tier → ℝ) : ℝ :=
  ∑ i : Tier, (classes i : ℝ) * probability i ^ 2 * w i

def cValue (w : Tier → ℝ) : ℝ :=
  ∑ i : Tier, (classes i : ℝ) * winner w i ^ 2

def aValue (w : Tier → ℝ) : ℝ :=
  ∑ i : Tier, (classes i : ℝ) * probability i * winner w i ^ 2

theorem h_kernelUpper_eq :
    hValue kernelUpper = (hNumerator:ℝ)/((R:ℝ)^2*(KQ:ℝ)) := by
  have hR : (R:ℝ) ≠ 0 := by norm_num [R]
  have hK : (KQ:ℝ) ≠ 0 := by norm_num [KQ]
  unfold hValue probability kernelUpper
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero 2 hR) hK)).2
  rw [Finset.sum_mul]
  unfold hNumerator
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hR,hK]

theorem c_kernelUpper_eq :
    cValue kernelUpper = (cNumerator:ℝ)/((R:ℝ)^2*(KQ:ℝ)^2) := by
  have hR : (R:ℝ) ≠ 0 := by norm_num [R]
  have hK : (KQ:ℝ) ≠ 0 := by norm_num [KQ]
  unfold cValue winner probability kernelUpper
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero 2 hR) (pow_ne_zero 2 hK))).2
  rw [Finset.sum_mul]
  unfold cNumerator
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hR,hK]

theorem a_kernelUpper_eq :
    aValue kernelUpper = (aNumerator:ℝ)/((R:ℝ)^3*(KQ:ℝ)^2) := by
  have hR : (R:ℝ) ≠ 0 := by norm_num [R]
  have hK : (KQ:ℝ) ≠ 0 := by norm_num [KQ]
  unfold aValue winner probability kernelUpper
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero 3 hR) (pow_ne_zero 2 hK))).2
  rw [Finset.sum_mul]
  unfold aNumerator
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hR,hK]

theorem h_le_kernelUpper {w : Tier → ℝ} (hw : KernelBounds w) :
    hValue w ≤ hValue kernelUpper := by
  unfold hValue
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hw.upper i)
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

theorem winner_nonneg {w : Tier → ℝ} (hw : KernelBounds w) (i : Tier) :
    0 ≤ winner w i := mul_nonneg (by unfold probability; positivity) (hw.nonneg i)

theorem winner_le_kernelUpper {w : Tier → ℝ} (hw : KernelBounds w) (i : Tier) :
    winner w i ≤ winner kernelUpper i := by
  unfold winner
  exact mul_le_mul_of_nonneg_left (hw.upper i) (by unfold probability; positivity)

theorem c_le_kernelUpper {w : Tier → ℝ} (hw : KernelBounds w) :
    cValue w ≤ cValue kernelUpper := by
  unfold cValue
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_left₀ (winner_nonneg hw i) (winner_le_kernelUpper hw i) 2
  · positivity

theorem a_le_kernelUpper {w : Tier → ℝ} (hw : KernelBounds w) :
    aValue w ≤ aValue kernelUpper := by
  unfold aValue
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_left₀ (winner_nonneg hw i) (winner_le_kernelUpper hw i) 2
  · exact mul_nonneg (Nat.cast_nonneg _) (by unfold probability; positivity)

theorem h_value_lt {w : Tier → ℝ} (hw : KernelBounds w) :
    hValue w < (967/1000)*kappa := by
  apply (h_le_kernelUpper hw).trans_lt
  rw [h_kernelUpper_eq]
  rw [show (hNumerator:ℝ)/((R:ℝ)^2*(KQ:ℝ)) = hRatio*kappa by
    unfold hRatio kappa
    push_cast
    field_simp]
  exact mul_lt_mul_of_pos_right hRatio_lt (by unfold kappa; positivity)

theorem c_value_lt {w : Tier → ℝ} (hw : KernelBounds w) :
    cValue w < (8/25)*(L:ℝ)*kappa := by
  apply (c_le_kernelUpper hw).trans_lt
  rw [c_kernelUpper_eq]
  have hL : (L:ℝ) ≠ 0 := by norm_num [L]
  rw [show (cNumerator:ℝ)/((R:ℝ)^2*(KQ:ℝ)^2) = cRatio*(L:ℝ)*kappa by
    unfold cRatio kappa
    push_cast
    field_simp [hL]]
  exact mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_right cRatio_lt (by norm_num [L] : (0:ℝ)<L))
    (by unfold kappa; positivity)

theorem a_value_lt {w : Tier → ℝ} (hw : KernelBounds w) :
    aValue w < (1/4)*(L:ℝ)*kappa^2 := by
  apply (a_le_kernelUpper hw).trans_lt
  rw [a_kernelUpper_eq]
  have hL : (L:ℝ) ≠ 0 := by norm_num [L]
  rw [show (aNumerator:ℝ)/((R:ℝ)^3*(KQ:ℝ)^2) = aRatio*(L:ℝ)*kappa^2 by
    unfold aRatio kappa
    push_cast
    field_simp [hL]]
  exact mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_right aRatio_lt (by norm_num [L] : (0:ℝ)<L))
    (sq_pos_of_pos (by unfold kappa; positivity))

theorem kernelNumerator_le_wMax (i : Tier) : kernelNumerator i ≤ wMax := by
  revert i
  decide +kernel

theorem winnerNumerator_le_gMax (i : Tier) :
    aliases i * kernelNumerator i ≤ gMax := by
  revert i
  decide +kernel

theorem diagonalNumerator_le (i : Tier) :
    aliases i * kernelNumerator i ^ 2 ≤ diagonalMax := by
  revert i
  decide +kernel

theorem w_value_lt {w : Tier → ℝ} (hw : KernelBounds w) (i : Tier) :
    w i < (4/5)*(L:ℝ) := by
  have hnat := kernelNumerator_le_wMax i
  have hcast : (kernelNumerator i : ℝ) ≤ (wMax:ℝ) := by exact_mod_cast hnat
  have hL : (0:ℝ) < L := by norm_num [L]
  calc
    w i ≤ kernelUpper i := hw.upper i
    _ ≤ (wMax:ℝ)/(KQ:ℝ) := by
      unfold kernelUpper
      exact div_le_div_of_nonneg_right hcast (by positivity)
    _ = wRatio*(L:ℝ) := by
      unfold wRatio
      push_cast
      field_simp [ne_of_gt hL]
    _ < (4/5)*(L:ℝ) := mul_lt_mul_of_pos_right wRatio_lt hL

theorem winner_value_lt {w : Tier → ℝ} (hw : KernelBounds w) (i : Tier) :
    winner w i < (17/40)*(L:ℝ)*kappa := by
  have hnat := winnerNumerator_le_gMax i
  have hcast : ((aliases i * kernelNumerator i : ℕ) : ℝ) ≤ (gMax:ℝ) := by
    exact_mod_cast hnat
  have hL : (0:ℝ) < L := by norm_num [L]
  calc
    winner w i ≤ winner kernelUpper i := winner_le_kernelUpper hw i
    _ ≤ (gMax:ℝ)/((R:ℝ)*(KQ:ℝ)) := by
      unfold winner probability kernelUpper
      rw [div_mul_div_comm]
      push_cast at hcast
      exact div_le_div_of_nonneg_right hcast (by positivity)
    _ = gRatio*(L:ℝ)*kappa := by
      unfold gRatio kappa
      push_cast
      field_simp [ne_of_gt hL]
    _ < (17/40)*(L:ℝ)*kappa := by
      exact mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_right gRatio_lt hL)
        (by unfold kappa; positivity)

def diagonalValue (w : Tier → ℝ) (i : Tier) : ℝ := probability i * w i ^ 2

theorem diagonal_value_lt {w : Tier → ℝ} (hw : KernelBounds w) (i : Tier) :
    diagonalValue w i < (13/40)*(L:ℝ)^2*kappa := by
  have hnat := diagonalNumerator_le i
  have hcast : ((aliases i * kernelNumerator i^2 : ℕ) : ℝ) ≤ (diagonalMax:ℝ) := by
    exact_mod_cast hnat
  have hL : (0:ℝ) < L := by norm_num [L]
  have hsq : w i ^ 2 ≤ kernelUpper i ^ 2 :=
    pow_le_pow_left₀ (hw.nonneg i) (hw.upper i) 2
  calc
    diagonalValue w i ≤ diagonalValue kernelUpper i := by
      unfold diagonalValue
      exact mul_le_mul_of_nonneg_left hsq (by unfold probability; positivity)
    _ ≤ (diagonalMax:ℝ)/((R:ℝ)*(KQ:ℝ)^2) := by
      rw [show diagonalValue kernelUpper i =
          (((aliases i * kernelNumerator i^2 : ℕ) : ℝ)) / ((R:ℝ)*(KQ:ℝ)^2) by
        unfold diagonalValue probability kernelUpper
        push_cast
        field_simp]
      exact div_le_div_of_nonneg_right hcast (by positivity)
    _ = diagonalRatio*(L:ℝ)^2*kappa := by
      unfold diagonalRatio kappa
      push_cast
      field_simp [ne_of_gt hL]
    _ < (13/40)*(L:ℝ)^2*kappa := by
      exact mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_right diagonalRatio_lt (sq_pos_of_pos hL))
        (by unfold kappa; positivity)

def positiveValue (w : Tier → ℝ) : ℝ :=
  ∑ i : Tier, (classes i:ℝ) * (aliases i:ℝ)/(R:ℝ) * w i *
    (positiveFactor i:ℝ) / (2*(remainingAliases:ℝ))

theorem positive_kernelUpper_eq : positiveValue kernelUpper = positiveRatio := by
  have hR : (R:ℝ) ≠ 0 := by norm_num [R]
  have hK : (KQ:ℝ) ≠ 0 := by norm_num [KQ]
  have hrem : (remainingAliases:ℝ) ≠ 0 := by
    rw [show remainingAliases = R-acceptedAliases by rfl, acceptedAliases_exact]
    norm_num [R]
  have hden : (positiveDenominator:ℝ) ≠ 0 := by
    unfold positiveDenominator
    push_cast
    positivity
  unfold positiveValue positiveRatio kernelUpper
  apply (eq_div_iff hden).2
  rw [Finset.sum_mul]
  unfold positiveNumerator positiveDenominator
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ((classes i:ℝ)*(aliases i:ℝ)*(kernelNumerator i:ℝ)*(positiveFactor i:ℝ)) *
        ((R:ℝ)*(R:ℝ)⁻¹) * ((KQ:ℝ)*(KQ:ℝ)⁻¹) *
        ((remainingAliases:ℝ)*(remainingAliases:ℝ)⁻¹) := by ring
    _ = _ := by
      rw [mul_inv_cancel₀ hR, mul_inv_cancel₀ hK, mul_inv_cancel₀ hrem]
      ring

theorem positive_value_lt {w : Tier → ℝ} (hw : KernelBounds w) :
    positiveValue w < 47/100 := by
  have hle : positiveValue w ≤ positiveValue kernelUpper := by
    unfold positiveValue
    apply Finset.sum_le_sum
    intro i hi
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (hw.upper i) (by positivity)
  exact hle.trans_lt (positive_kernelUpper_eq.trans_lt positiveRatio_lt)

/-! ## Exact telescoping of true winner mass -/

/-- The list of exclusive accepted masses, in full 256-bit alias units. -/
def tierMasses : List ℕ := List.zipWith (·*·) classCounts aliasCounts

@[simp] theorem tierMasses_length : tierMasses.length = 160 := by decide +kernel

theorem tierMasses_sum : tierMasses.sum = acceptedAliases := by
  decide +kernel

def survival (pfx : ℕ) : ℝ := 1 - (pfx:ℝ)/(R:ℝ)

def tierMass (i : Tier) : ℕ := classes i * aliases i
def prefixMass (i : Tier) : ℕ := (tierMasses.take i.val).sum

theorem tierMass_pos (i : Tier) : 0 < tierMass i := by
  revert i
  decide +kernel

theorem prefix_add_mass_le (i : Tier) :
    prefixMass i + tierMass i ≤ acceptedAliases := by
  revert i
  decide +kernel

theorem prefix_add_mass_lt_R (i : Tier) : prefixMass i + tierMass i < R :=
  (prefix_add_mass_le i).trans_lt acceptedAliases_bounds.2

theorem prefix_lt_R (i : Tier) : prefixMass i < R := by
  have h := prefix_add_mass_lt_R i
  omega

theorem survival_nonneg_of_le {c : ℕ} (hc : c ≤ R) : 0 ≤ survival c := by
  unfold survival
  apply sub_nonneg.mpr
  apply (div_le_one (by norm_num [R] : (0:ℝ)<R)).2
  exact_mod_cast hc

def Q : ℕ := R^2

def squareLower (n : ℕ) : ℕ := n^2 / Q
def squareUpper (n : ℕ) : ℕ := n^2 ⌈/⌉ Q

def iterateLower : ℕ → ℕ → ℕ
  | 0, n => n
  | s+1, n => squareLower (iterateLower s n)

def iterateUpper : ℕ → ℕ → ℕ
  | 0, n => n
  | s+1, n => squareUpper (iterateUpper s n)

theorem Q_pos : 0 < Q := by norm_num [Q,R]

theorem squareLower_ratio_le (n : ℕ) :
    (squareLower n : ℝ)/(Q:ℝ) ≤ ((n:ℝ)/(Q:ℝ))^2 := by
  have hn : squareLower n * Q ≤ n^2 := by
    unfold squareLower
    exact Nat.div_mul_le_self _ _
  have hn' : (squareLower n : ℝ)*(Q:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hn
  have hQ : (0:ℝ)<Q := by exact_mod_cast Q_pos
  rw [div_pow]
  apply (div_le_div_iff₀ hQ (sq_pos_of_pos hQ)).2
  calc
    (squareLower n:ℝ) * (Q:ℝ)^2 = ((squareLower n:ℝ)*(Q:ℝ))*(Q:ℝ) := by ring
    _ ≤ (n:ℝ)^2*(Q:ℝ) := mul_le_mul_of_nonneg_right hn' hQ.le

theorem squareUpper_ratio_ge (n : ℕ) :
    ((n:ℝ)/(Q:ℝ))^2 ≤ (squareUpper n : ℝ)/(Q:ℝ) := by
  have hn : n^2 ≤ Q * squareUpper n := by
    unfold squareUpper
    exact (ceilDiv_le_iff_le_mul Q_pos).mp le_rfl
  have hn' : (n:ℝ)^2 ≤ (Q:ℝ)*(squareUpper n:ℝ) := by exact_mod_cast hn
  have hQ : (0:ℝ)<Q := by exact_mod_cast Q_pos
  rw [div_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos hQ) hQ).2
  calc
    (n:ℝ)^2*(Q:ℝ) ≤ ((Q:ℝ)*(squareUpper n:ℝ))*(Q:ℝ) :=
      mul_le_mul_of_nonneg_right hn' hQ.le
    _ = (squareUpper n:ℝ)*(Q:ℝ)^2 := by ring

theorem iterateLower_bound (s n : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (h : (n:ℝ)/(Q:ℝ) ≤ x) :
    (iterateLower s n:ℝ)/(Q:ℝ) ≤ x^(2^s) := by
  induction s with
  | zero => simpa [iterateLower] using h
  | succ s ih =>
      calc
        (iterateLower (s+1) n:ℝ)/(Q:ℝ) =
            (squareLower (iterateLower s n):ℝ)/(Q:ℝ) := rfl
        _ ≤ (((iterateLower s n:ℝ)/(Q:ℝ)))^2 := squareLower_ratio_le _
        _ ≤ (x^(2^s))^2 := pow_le_pow_left₀ (by positivity) ih 2
        _ = x^(2^(s+1)) := by rw [← pow_mul, pow_succ]

theorem iterateUpper_bound (s n : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (h : x ≤ (n:ℝ)/(Q:ℝ)) :
    x^(2^s) ≤ (iterateUpper s n:ℝ)/(Q:ℝ) := by
  induction s with
  | zero => simpa [iterateUpper] using h
  | succ s ih =>
      calc
        x^(2^(s+1)) = (x^(2^s))^2 := by rw [← pow_mul, pow_succ]
        _ ≤ (((iterateUpper s n:ℝ)/(Q:ℝ)))^2 :=
          pow_le_pow_left₀ (pow_nonneg hx _) ih 2
        _ ≤ (squareUpper (iterateUpper s n):ℝ)/(Q:ℝ) := squareUpper_ratio_ge _
        _ = (iterateUpper (s+1) n:ℝ)/(Q:ℝ) := rfl

def baseNumerator (c : ℕ) : ℕ := (R-c)*R

theorem baseNumerator_ratio {c : ℕ} (hc : c ≤ R) :
    (baseNumerator c:ℝ)/(Q:ℝ) = survival c := by
  have hR : (R:ℝ) ≠ 0 := by norm_num [R]
  unfold baseNumerator Q survival
  rw [Nat.cast_mul, Nat.cast_sub hc, Nat.cast_pow]
  field_simp [hR]

def powerLower (c : ℕ) : ℕ := iterateLower 20 (baseNumerator c)
def powerUpper (c : ℕ) : ℕ := iterateUpper 20 (baseNumerator c)

theorem powerLower_bound {c : ℕ} (hc : c ≤ R) :
    (powerLower c:ℝ)/(Q:ℝ) ≤ survival c ^ L := by
  have hs := survival_nonneg_of_le hc
  have h := iterateLower_bound 20 (baseNumerator c) hs (le_of_eq (baseNumerator_ratio hc))
  simpa [powerLower,L] using h

theorem powerUpper_bound {c : ℕ} (hc : c ≤ R) :
    survival c ^ L ≤ (powerUpper c:ℝ)/(Q:ℝ) := by
  have hs := survival_nonneg_of_le hc
  have h := iterateUpper_bound 20 (baseNumerator c) hs (le_of_eq (baseNumerator_ratio hc).symm)
  simpa [powerUpper,L] using h

theorem rounded_order (i : Tier) :
    powerLower (prefixMass i+tierMass i) ≤ powerUpper (prefixMass i) := by
  revert i
  decide +kernel

theorem rounded_kernel_integer (i : Tier) :
    R * (powerUpper (prefixMass i) - powerLower (prefixMass i+tierMass i)) * KQ ≤
      kernelNumerator i * tierMass i * Q := by
  revert i
  decide +kernel

def actualKernel (i : Tier) : ℝ :=
  kernel L (survival (prefixMass i)) (survival (prefixMass i+tierMass i))

theorem actualKernel_nonneg (i : Tier) : 0 ≤ actualKernel i := by
  unfold actualKernel
  apply kernel_nonneg
  · exact survival_nonneg_of_le (prefix_lt_R i).le
  · exact survival_nonneg_of_le (prefix_add_mass_lt_R i).le

theorem rounded_difference_le (i : Tier) :
    survival (prefixMass i)^L - survival (prefixMass i+tierMass i)^L ≤
      ((powerUpper (prefixMass i) - powerLower (prefixMass i+tierMass i):ℕ):ℝ)/(Q:ℝ) := by
  have hu := powerUpper_bound (prefix_lt_R i).le
  have hl := powerLower_bound (prefix_add_mass_lt_R i).le
  have ho := rounded_order i
  rw [Nat.cast_sub ho]
  rw [sub_div]
  linarith

theorem rounded_ratio_le (i : Tier) :
    ((powerUpper (prefixMass i) - powerLower (prefixMass i+tierMass i):ℕ):ℝ)/(Q:ℝ) ≤
      ((tierMass i:ℝ)/(R:ℝ))*((kernelNumerator i:ℝ)/(KQ:ℝ)) := by
  have hn := rounded_kernel_integer i
  have hn' :
      (R:ℝ) * ((powerUpper (prefixMass i) - powerLower (prefixMass i+tierMass i):ℕ):ℝ) * (KQ:ℝ) ≤
        (kernelNumerator i:ℝ) * (tierMass i:ℝ) * (Q:ℝ) := by
    exact_mod_cast hn
  have hR : (0:ℝ)<R := by norm_num [R]
  have hQ : (0:ℝ)<Q := by exact_mod_cast Q_pos
  have hK : (0:ℝ)<KQ := by norm_num [KQ]
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ hQ (mul_pos hR hK)).2
  nlinarith

theorem survival_sub (i : Tier) :
    survival (prefixMass i) - survival (prefixMass i+tierMass i) =
      (tierMass i:ℝ)/(R:ℝ) := by
  unfold survival
  have hR : (R:ℝ) ≠ 0 := by norm_num [R]
  push_cast
  field_simp [hR]
  ring

theorem actualKernel_le (i : Tier) : actualKernel i ≤ kernelUpper i := by
  have hp : 0 < (tierMass i:ℝ)/(R:ℝ) := by
    exact div_pos (by exact_mod_cast tierMass_pos i) (by norm_num [R])
  have hk := sub_mul_kernel L (survival (prefixMass i))
    (survival (prefixMass i+tierMass i))
  rw [survival_sub i] at hk
  have hprod :
      ((tierMass i:ℝ)/(R:ℝ))*actualKernel i ≤
        ((tierMass i:ℝ)/(R:ℝ))*kernelUpper i := by
    calc
      ((tierMass i:ℝ)/(R:ℝ))*actualKernel i =
          survival (prefixMass i)^L-survival (prefixMass i+tierMass i)^L := by
        exact hk
      _ ≤ ((powerUpper (prefixMass i) - powerLower (prefixMass i+tierMass i):ℕ):ℝ)/(Q:ℝ) :=
        rounded_difference_le i
      _ ≤ ((tierMass i:ℝ)/(R:ℝ))*((kernelNumerator i:ℝ)/(KQ:ℝ)) :=
        rounded_ratio_le i
      _ = ((tierMass i:ℝ)/(R:ℝ))*kernelUpper i := by rfl
  exact le_of_mul_le_mul_left hprod hp

theorem actualKernel_bounds : KernelBounds actualKernel where
  nonneg := actualKernel_nonneg
  upper := actualKernel_le


/-- The actual finite-difference kernels satisfy every checked moment envelope. -/
theorem actual_h_lt : hValue actualKernel < (967/1000)*kappa :=
  h_value_lt actualKernel_bounds

theorem actual_c_lt : cValue actualKernel < (8/25)*(L:ℝ)*kappa :=
  c_value_lt actualKernel_bounds

theorem actual_a_lt : aValue actualKernel < (1/4)*(L:ℝ)*kappa^2 :=
  a_value_lt actualKernel_bounds

theorem actual_w_lt (i : Tier) : actualKernel i < (4/5)*(L:ℝ) :=
  w_value_lt actualKernel_bounds i

theorem actual_g_lt (i : Tier) : winner actualKernel i < (17/40)*(L:ℝ)*kappa :=
  winner_value_lt actualKernel_bounds i

theorem actual_diagonal_lt (i : Tier) :
    diagonalValue actualKernel i < (13/40)*(L:ℝ)^2*kappa :=
  diagonal_value_lt actualKernel_bounds i

theorem actual_positive_lt : positiveValue actualKernel < 47/100 :=
  positive_value_lt actualKernel_bounds

/-- Sum of the actual (not rounded) tier winner masses from a given prefix. -/
def winnerMassSum (pfx : ℕ) : List ℕ → ℝ
  | [] => 0
  | m :: ms =>
      (m:ℝ)/(R:ℝ) * kernel L (survival pfx) (survival (pfx+m)) +
        winnerMassSum (pfx+m) ms

theorem winnerMassSum_telescope (pfx : ℕ) (ms : List ℕ) :
    winnerMassSum pfx ms =
      survival pfx ^ L - survival (pfx + ms.sum) ^ L := by
  induction ms generalizing pfx with
  | nil => simp [winnerMassSum]
  | cons m ms ih =>
      rw [winnerMassSum, ih]
      have hdiff : survival pfx - survival (pfx+m) = (m:ℝ)/(R:ℝ) := by
        unfold survival R
        norm_num
        ring
      have hk := sub_mul_kernel L (survival pfx) (survival (pfx+m))
      rw [← hdiff, hk]
      simp only [List.sum_cons, Nat.add_assoc]
      ring

/-- Exact telescoping bound `sum_i n_i g_i = 1 - failure < 1` for the true kernels. -/
theorem exact_sum_g :
    winnerMassSum 0 tierMasses =
      1 - (1-(acceptedAliases:ℝ)/(R:ℝ))^L := by
  rw [winnerMassSum_telescope, tierMasses_sum]
  simp [survival]

theorem exact_sum_g_lt_one : winnerMassSum 0 tierMasses < 1 := by
  rw [exact_sum_g]
  have hb : 0 < 1-(acceptedAliases:ℝ)/(R:ℝ) := by
    rw [acceptedAliases_exact]
    norm_num [R]
  have hp : 0 < (1-(acceptedAliases:ℝ)/(R:ℝ))^L := pow_pos hb L
  linarith

/-! ## Collision-aware availability -/

def collisionAliases : ℕ := 2^190

def replacementBase : ℝ :=
  1 - (acceptedAliases:ℝ)/(R:ℝ) + (L:ℝ)/(2:ℝ)^86

theorem collisionAliases_eq :
    (L:ℝ)/(2:ℝ)^86 = (collisionAliases:ℝ)/(R:ℝ) := by
  norm_num [L,R,collisionAliases]

theorem replacementBase_effective :
    replacementBase = 1-((acceptedAliases-collisionAliases:ℕ):ℝ)/(R:ℝ) := by
  have hc : collisionAliases ≤ acceptedAliases := by
    rw [acceptedAliases_exact]
    norm_num [collisionAliases]
  rw [replacementBase, collisionAliases_eq, Nat.cast_sub hc]
  ring

theorem replacementBase_nonneg : 0 ≤ replacementBase := by
  unfold replacementBase
  rw [acceptedAliases_exact]
  norm_num [R,L]

theorem replacementBase_lt_reference :
    replacementBase < 1-(8999:ℝ)/104857600 := by
  unfold replacementBase
  rw [acceptedAliases_exact]
  norm_num [R,L]

/-- With-replacement nonce collisions included, honest signing failure is strictly below `2^-129`. -/
theorem collisionAwareAvailability :
    replacementBase^L < ((2:ℝ)^129)⁻¹ := by
  have hpow : replacementBase^L < (1-(8999:ℝ)/104857600)^L :=
    pow_lt_pow_left₀ replacementBase_lt_reference replacementBase_nonneg (by norm_num [L])
  exact hpow.trans_le (by
    simpa only [L] using _root_.WeightedAvailability.empirical_failure)

#print axioms familyCardinality_exact
#print axioms acceptedAliases_exact
#print axioms moment_envelopes
#print axioms exact_sum_g
#print axioms collisionAwareAvailability

end
end OptimalOTS.Chain18Compact
