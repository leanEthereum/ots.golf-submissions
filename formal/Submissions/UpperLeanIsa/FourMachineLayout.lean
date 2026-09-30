import Submissions.UpperLeanIsa.PrefixCache
import Submissions.UpperLeanIsa.FieldRescale
import Submissions.UpperLeanIsa.SplitDomains
import Submissions.UpperLeanIsa.LengthGate128

/-! Layout of the fixed-tag fused machine. All live field bands begin at raw field zero;
the excluded zero-cost binding tuples have no holes or aliases. The 27-slot prologue is
followed by 13 group regions ending at slot 252171. Unit 11's blocks start at slots whose
`g ^ e` carries their field value (`HintTie`); the other groups are packed by cost band.
Free-chain blocks remain at 255615 + 68*s. -/

namespace OptimalOTS.HLFour

open LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits cellOfBits)
open OptimalOTS.HLG3 (natV)

/-! ## Exponent arithmetic -/

/-- The order of `g`, `2 ^ 64 - 1`, as a literal (so `omega` can reduce modulo it). -/
def ordG : ℕ := 18446744073709551615

theorem ordG_eq : ordG = 2 ^ 64 - 1 := by norm_num [ordG]

theorem gpow_mod (n : ℕ) : gpow (n % ordG) = gpow n := by
  rw [ordG_eq, ← OptimalOTS.GenFast.orderOf_g]; exact pow_mod_orderOf g n

theorem mod_ord_of_lt {n : ℕ} (h : n < ordG) : n % ordG = n := Nat.mod_eq_of_lt h

theorem mod_ord_of_ge {n : ℕ} (h : ordG ≤ n) (h' : n < 2 * ordG) : n % ordG = n - ordG := by
  rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

theorem gpow_mul_gpow (a b : ℕ) : gpow a * gpow b = gpow (a + b) := (pow_add g a b).symm

theorem gpow_zero' : gpow 0 = 1 := pow_zero g

theorem g_mul_gpow (k : ℕ) : g * gpow k = gpow (k + 1) := (gpow_succ k).symm

/-- `gpow` is injective below the group order. -/
theorem gpow_inj {a b : ℕ} (ha : a < 2 ^ 64 - 1) (hb : b < 2 ^ 64 - 1) (h : gpow a = gpow b) :
    a = b := OptimalOTS.GenFast.gpow_injOn (Set.mem_Iio.mpr ha) (Set.mem_Iio.mpr hb) h

/-! ## Partial sums and bands -/

/-- `F 0 + ⋯ + F (c - 1)`. -/
def psum (F : ℕ → ℕ) (c : ℕ) : ℕ := ∑ i ∈ Finset.range c, F i

theorem psum_zero (F : ℕ → ℕ) : psum F 0 = 0 := rfl

theorem psum_succ (F : ℕ → ℕ) (c : ℕ) : psum F (c + 1) = psum F c + F c :=
  Finset.sum_range_succ F c

theorem psum_mono (F : ℕ → ℕ) : Monotone (psum F) := fun _ _ h =>
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

/-- The band of `o` under the boundaries `F 0 ≤ F 1 ≤ ⋯ ≤ F N`: the number of `c < N` with
`F (c + 1) ≤ o`. -/
def bandIdx (F : ℕ → ℕ) (N o : ℕ) : ℕ := ((Finset.range N).filter (fun c => F (c + 1) ≤ o)).card

theorem bandIdx_eq {F : ℕ → ℕ} (hF : Monotone F) {N c o : ℕ} (hc : c < N) (h1 : F c ≤ o)
    (h2 : o < F (c + 1)) : bandIdx F N o = c := by
  unfold bandIdx
  have : (Finset.range N).filter (fun c' => F (c' + 1) ≤ o) = Finset.range c := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hle⟩
      by_contra hxc
      have := hF (show c + 1 ≤ x + 1 by omega)
      omega
    · intro hx
      exact ⟨by omega, le_trans (hF (show x + 1 ≤ c by omega)) h1⟩
  rw [this, Finset.card_range]

theorem bandIdx_spec {F : ℕ → ℕ} (hF : Monotone F) {N o : ℕ} (h0 : F 0 ≤ o) (hN : o < F N) :
    bandIdx F N o < N ∧ F (bandIdx F N o) ≤ o ∧ o < F (bandIdx F N o + 1) := by
  have hN0 : N ≠ 0 := by rintro rfl; omega
  have hex : ∃ c, o < F (c + 1) := ⟨N - 1, by rwa [Nat.sub_add_cancel (by omega)]⟩
  classical
  set c := Nat.find hex with hc
  have hspec : o < F (c + 1) := Nat.find_spec hex
  have hle : c ≤ N - 1 := Nat.find_min' hex (by rwa [Nat.sub_add_cancel (by omega)])
  have hlo : F c ≤ o := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h]; exact h0
    · have := Nat.find_min hex (show c - 1 < c by omega)
      rw [Nat.sub_add_cancel h] at this
      omega
  rw [bandIdx_eq hF (show c < N by omega) hlo hspec]
  exact ⟨by omega, hlo, hspec⟩

/-! ## Groups -/

/-- Groups 5 and 6 have four chains; every other group has three. -/
def gk (u : ℕ) : ℕ := if u = 5 ∨ u = 6 then 4 else 3

/-- The index field width of group `u`. -/
def gb (u : ℕ) : ℕ := [10, 9, 9, 9, 9, 12, 11, 10, 10, 10, 10, 9, 10].getD u 0

/-- The bit position of group `u`'s field. -/
def POS (u : ℕ) : ℕ := posW gb u

/-- Groups that materialize each top, including zero-digit disclosures. -/
def isExp (u : ℕ) : Prop := u ≠ 5

instance (u : ℕ) : Decidable (isExp u) := by unfold isExp; infer_instance

/-- The padded group budget plus one. The straight body uses `gcu - 2`
ordinary instructions and its affine dispatch uses one: total `gcu - 1`. -/
def gcu (u : ℕ) : ℕ := [7, 8, 8, 8, 8, 6, 7, 8, 8, 8, 8, 6, 7].getD u 6

/-- The single root call executes in group 5. -/
def hm (u : ℕ) : ℕ := if u = 5 then 1 else 0

/-- Raw field-value counts in each live cost band. -/
def prof (u : ℕ) : List ℕ :=
  ([[0, 6, 12, 20, 30, 42, 56, 72, 90, 110, 132, 156, 182, 116, 0, 0, 0, 0], [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 57, 0, 0, 0, 0], [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 57, 0, 0, 0, 0], [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 57, 0, 0, 0, 0], [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 57, 0, 0, 0, 0], [0, 499, 10, 20, 37, 56, 88, 120, 165, 220, 286, 376, 457, 560, 680, 522, 0, 0], [0, 10, 7, 17, 30, 50, 77, 118, 156, 210, 275, 352, 442, 304, 0, 0, 0, 0], [1, 6, 14, 10, 30, 21, 30, 38, 48, 55, 66, 78, 91, 105, 120, 133, 150, 0], [0, 9, 18, 33, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 146, 150, 8], [0, 12, 12, 12, 30, 26, 28, 38, 45, 56, 66, 78, 91, 105, 120, 136, 150, 19], [0, 27, 12, 10, 15, 35, 28, 36, 45, 55, 66, 78, 91, 105, 120, 136, 150, 15], [0, 2, 5, 9, 14, 20, 27, 35, 44, 54, 65, 80, 90, 67, 0, 0, 0, 0], [0, 145, 8, 9, 14, 20, 27, 35, 44, 54, 73, 77, 90, 104, 119, 135, 70, 0]]).getD u []

/-- Number of cost bands of group `u` (maximal cost plus one). -/
def nb (u : ℕ) : ℕ := (prof u).length

/-- Number of table tuples of cost `c` in group `u`. -/
def pn (u c : ℕ) : ℕ := (prof u).getD c 0

/-- Field values of cost below `c`: the band of cost `c` is `[A u c, A u (c + 1))`. -/
def AData : Nat := 506149843973522142453347945260130287915383522612230616111530840661092694018934183712544955297996543346929909637307603759281677350342436442452483588313577405440741868144262676320815198753012718296641545254132438886169357630789378764857254808890970559124472963137174662750181595880161245359894680573253571227697662522215983827499472956419669369574357636061018082350625016301316681557879212685431885770232052663850368387350809948311044353346369194699183934023495270889805696154618273633827459808766276566492850823383656435545774729394880045077915247719717597922348145208848853778599644073107099120770654641439457128196842985568827597313675173334311632847443805852470889737885418294321003202904912322683467955316268284227568500139510418133201703171847342364423786918205824520686822612415338344494323005543439210322193407746776385095659772475075816231742129941096214638615481601905513121840220716306291353348753674798499503031927383993203772780275113029717967422225383424
def ATable (u c : Nat) : Nat :=
  CheckedPrefix.read AData 13 (Nat.add (Nat.mul 19 u) c)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ATable_checked : ((List.range 13).all fun u =>
    CheckedPrefix.check (pn u) (ATable u) 18) = true := rfl

def A (u c : Nat) : Nat :=
  if u < 13 ∧ c ≤ 18 then ATable u c else psum (pn u) c

theorem A_eq (u c : Nat) : A u c = psum (pn u) c := by
  unfold A
  split_ifs with h
  · have ht := List.all_eq_true.mp ATable_checked u (List.mem_range.mpr h.1)
    exact CheckedPrefix.correct _ _ ht h.2
  · rfl

/-- Block length of cost `c` in group `u`. -/
def L (u c : ℕ) : ℕ := gcu u - 1 + c + hm u

/-- Slot offset of cost band `c` in group `u`'s region. -/
def OFFData : Nat := 151251319425940665430510452696292670042774305425433601484092358207100703339653194736634786021202444195389552502265511324915331249301722711449480149201018733701425976778133300148607712986118005514196718594530114623754056123899469671341465114209703211280191822192442974312952157640306658086314038637173867773331883233174747424068237723119499167823473767439368378762191824321802510473024782603483279311347575244977360175003022096676170078790782720896302894160080906319157924704976336981183037536246233678669920864270811745861479606609009800753341932934508422947802074233110210788401492238577649980762911684871239292264833528518069827705139230679488795572827028144451622124731663741758795209671555384824689836118513753106864607367963366651099209467719309644539566368761952727428758222877656890534641011617063397409556018057462102804073840961943907817294822102353963682261838913761126138534767973524261272140899470357955437958361660763747131592658226556253295772615449527259046336089523966871150633150976677929776417904895379953081627169197609299285964211923893922388626269247543719119224791759367958310108718331422833120884889849179982554189759364380112533089138310469061449810178704236855508209272571860262839819056084155921885873110056717675917687740139077882873230575866055267148254618083231510427863667264377024961290279810481318256443392
def OFFTable (u c : Nat) : Nat :=
  CheckedPrefix.read OFFData 18 (Nat.add (Nat.mul 19 u) c)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem OFFTable_checked : ((List.range 13).all fun u =>
    CheckedPrefix.check (fun c => pn u c * L u c) (OFFTable u) 18) = true := rfl

def OFF (u c : Nat) : Nat :=
  if u < 13 ∧ c ≤ 18 then OFFTable u c else psum (fun c => pn u c * L u c) c

theorem OFF_eq (u c : Nat) : OFF u c = psum (fun c => pn u c * L u c) c := by
  unfold OFF
  split_ifs with h
  · have ht := List.all_eq_true.mp OFFTable_checked u (List.mem_range.mpr h.1)
    exact CheckedPrefix.correct _ _ ht h.2
  · rfl

/-- Unit 11 packs its blocks in slot order `j`: block `j` holds field value `ord11 j` and
spans `gap11 j` slots. Each block starts at a slot `e` whose `g ^ e` has field value in bits
28..36 (`HintTie.gpow_entry11`); the slots after its control op are trap pads. The tables are
packed naturals: entry `j` of a `w`-bit table `N` is `N / 2 ^ (w * j) % 2 ^ w`. -/
def gap11N : ℕ := 0x10ca3344266783442f1c111b501f120d294a0f473f12110e121f1b1e17131227171b1627122411122d11191828141a111b10270f133316111115180d331227121e250e12140e1a0f131e1c18121712160e0d1717131912121113160d0f131514170c211d12101a1511110f11112112110f0c1119181714150d171210130e1312120e131a110e12131311120815160d110e131010100f1716181116261a120f1019141015140c110c24190a12140d11120e100b0c1511171216121014130911150d0f1611100f1011110d131e10120d160e0f21101009100f0e1112150c12140d0d1411100c0d1114080d120d10110e110d110f17120e0f120f1010190f12100f10120f0c110f12110b1309100b13110b0f120b1311120b0f11100c120a130e1014110e0f1013131211181310130a0f0a080f0e101212100b0f0b100c0b110e120e0c10121411100c0e101211121110100f111211100e0c0f0f0c0c0b100f12140f120a110d110e0e120d100e110d121108100f110f12121012100e140c0b1111120d100f0711100c10090d061211110710121212110f0e1213110f0c1112110d0d0d0b0a0d0a0c120c10090e0c0f110c0f0e101008100c0b0f130b100d0e120f11101112100e10110c0d07120f081010120f110f0d09060f1012110c0811090c0b1110110f12110a0a110a080f0e110b0b100d120e11100912120c0c0a0c1211
def ord11N : ℕ := 0xa404524e045930f5518426021bd7476a0429d5ec1e3176c698e82af62818968ad53f017aaa8c56bd5aea0115839cedb786aa2f2b42eda4aacdd0a6f9254906cf75f6e6279f9a87de6ad090a458c2b234a1fb64ef9d4b632ec408630df5fcfe3433c36f3eae17a75424d2b96a9d1423ddca8367d56075e9ddc6b1d51b2d7b7d895de64ade1b9de52ae53f4d19faa0299c41aba4720acb3b76b9ab67dbc0a60f6cf3b85a0a226304e8f95a869086a71ee2bc061303d2390e124ff84aee56f1d84337fe1a3955eb5b3e0445a61de1a7cc97f34e347d285769793bb1d3d35748e257a8ba25f80cf3b2fca9c864b5e952da68769cc066b9bc9a3306fc9c894b6814aa7292472f810693fea618a37161693e61147f3fbac503d05f0d237953fd955ef025ee9ac5b7e2227d8e176b4130b197b64a406979c85f182614950e93ca46bfe1376595309920934ea8ad8ebfd6b3e66eb16e584df21e032892b338e7620e3c7b0f67647245c18bc23f0edcbb5c7e4250415e4779372e9e61a1587be77df9171a1cbd123790c881fa03b3f1e87a7f45f2a46445849cf1242a87bb71b7bb8c05d121f666d7cae6f5efcf567a9340d9fb87df24ebce202ee678678f86cbe019bb873403a0fe759c7c6be977d2c566e1a58c46cb24721fa642e27468b4cbc4362c81c9f31b52fc5d73ade972e03d309a46537f043573c331ff05d9c9b17825d3226d71299cc09fb8803e3353e2c0312f24a06000dd917c2da59016882c6919eaa59767f7475c2015ec4580c6daa6fa3911cc537c147d92a41cfa780a25c1219bd36b
def pos11N : ℕ := 0xadb913c461a614dca185ede2a0786229d82656d91e5e7a866402a07770b1125aba5f520643f01239cb97c9c4cae3363b9b4599a03508d66268d4869f496b30366ac5e58a9b001935911ffe9d5bcbf8f570e2f5979411f9882deed6865ec6df78790938cb7aa875f9208ba31ebb71d5d80331c5acb28ce460986db18558ba5dbe0d6901e99c5a6340629d50eec0f231e1aa14423b5c8782814aac871ab3744ad070c2d424c4bb30068221e46ba32040a6d6c6ad986c9f7b7a1c5f8ef6b0225dfbe9518027f19bf14a6564a26cb79fffa264ba68ee0ef8dea3c1be50c7962e7faf65398e679a26637c1ce0a3932581d9ca71ccb9738f9e35cbe89ecf7c3be756ccb82ee463bbf6351b713b6aa1343346ba0cbaa7a732c3f764f2080ebb07c6c42e2086d02fbc79a9a34e57b1d109fe18b3db00c6e57a0a2cbb7277f327c997b5e559f0e5fce5dd4511209a2f35eb973f77e52a4bbf08b19a5ea4e42d93865e3a9f6bd83e5a5a66e7289941f4ab7348eef1a62753fbb6f4295a151180dfad3bae754425828e11e3bc986b3b71e62a4f6d69806b74bdf69b47d9a2b3f7f6349605d48b69bfdf6640fa555a37ba3bfb7a13da81aff4f0f4a7e6e2439fccf49e91b1828b5d53f352457ca75040833c008b38c29f1229233aaa4a0047e5304864b1d630f311bc6c0b9e8b48493fa7fba794c36212378a5533b570f02fda98cc85f64c213ad7209cb060fbcfbd6c4ebdcb4150bfa3e16e2e38f1c0307d348a185234254083b59aaa2a2e88685816956bfdf5191562e1447dd1ebb025b3cf6353808ce829

def gap11 (j : ℕ) : ℕ := gap11N / 2 ^ (8 * j) % 2 ^ 8
def ord11 (j : ℕ) : ℕ := ord11N / 2 ^ (9 * j) % 2 ^ 9
def pos11 (v : ℕ) : ℕ := pos11N / 2 ^ (9 * v) % 2 ^ 9

/-- Offset of unit 11's block `j` in its region. -/
def bd11Slow : ℕ → ℕ
  | 0 => 0
  | j + 1 => bd11Slow j + gap11 j

/-- Certified prefix sums avoid expanding the 512-step sum at every use. -/
def bd11Data : Nat := 58172551204888282068535570465046820928700157792647547775807243257903951871729436202079866020332182428518185971405539029581728550818763241991917267789787039741303831898740672475490636817956102449772042727218371489237332018169101097131436588580980675545642144192440711144805174260519079373091163515452362363104407175650013955810389072436219100541191571883964782706414627160553994081893619619953821640302799971042851434819743755030562633170056694066011339932099974593194865744120086506286728287859799743418964668540587203888309548063279169763271043757574905029537588583963011433979441516435449800654924074620139519180415365366781113525796837244094355428651694296215944052052900544455728278240899963511966885117139040490204416254367048976084888508946257187687999356362360656850759914562659201442461557657760409544925895992780344007528198741169068453300549014778890518807223756740382271014572902243318008817065367145249824499883227129204118182679738418940024569718245828392129425580899123321346612018798374397735508879757967433294993381830855241944556472755865612706206401843489296968794342611406059423520744180531793764562063408142546388196574265781666537516415321963627318040748126698817291673514852065132737311820152898374796485180962939803278158928138238637836131053753550042741502118061474996482209695403125706165141247861966061304402614888047352517474593071407188132240583291786492316940226452080041365562943707464303797178528553689606032376308715898192198853381063857028117686939410782069829140479888431518068819161391594290702802730717781241505766308257059060325566742944643245302715797596836496237188905454181938286264838343895766328283712720885391297107438405701587073863540143208372798844036821842974874348875398107737942187721755261718686596160320478065782926669187694175217475854674789635822929156676375936343162449149706001568075088189480116197542183622502203732323583954823332400966880017754860776866667767044571011892423868606200999548684150954836825292154247454171711120399912943734196104384244379859159100926348799139667181280497137743094597934636459501978275595048977018097394104685483910524339084640682152288819508662407154656923297479098571702272
def bd11Table (j : Nat) : Nat :=
  Nat.land (Nat.shiftRight bd11Data (Nat.mul 14 j)) 16383

theorem bd11Table_zero : bd11Table 0 = 0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 10000 in
theorem bd11Table_checked : ((List.range 512).all fun j =>
    Nat.beq (bd11Table (j+1)) (Nat.add (bd11Table j) (gap11 j))) = true := rfl

theorem bd11Table_correct : ∀ j, j ≤ 512 → bd11Table j = bd11Slow j
  | 0, _ => bd11Table_zero
  | j+1, hj => by
    have h := List.all_eq_true.mp bd11Table_checked j (List.mem_range.mpr (by omega))
    have he := Nat.beq_eq.mp h
    rw [bd11Table_correct j (by omega)] at he
    exact he

def bd11 (j : Nat) : Nat := if j ≤ 512 then bd11Table j else bd11Slow j

theorem bd11_eq_slow (j : Nat) : bd11 j = bd11Slow j := by
  unfold bd11
  split_ifs with h
  · exact bd11Table_correct j h
  · rfl

/-- Size of group `u`'s region. -/
def RS (u : ℕ) : ℕ := if u = 11 then bd11 512 else OFF u (nb u)

/-- First slot of group `u`'s region (the prologue is slots `0 … 26`). -/
def BASEData : Nat := 6960960534179540073037407049646618157417555934039760335288653128278682894336
def BASETable (u : Nat) : Nat := CheckedPrefix.read BASEData 18 u

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem BASETable_checked : CheckedPrefix.check RS BASETable 13 = true := rfl

def BASE (u : Nat) : Nat := 27 + if u ≤ 13 then BASETable u else psum RS u

theorem BASE_eq (u : Nat) : BASE u = 27 + psum RS u := by
  unfold BASE
  split_ifs with h
  · rw [CheckedPrefix.correct _ _ BASETable_checked h]
    rfl
  · rfl

/-- End of the group regions. -/
def gEnd : ℕ := 252171

/-- The number of blocks (live field values) of group `u`: the live values are a contiguous prefix. -/
def VF (u : ℕ) : ℕ := [1024, 512, 512, 512, 512, 4096, 2048, 996, 1024, 1024, 1024, 512, 1024].getD u 0

/-- The cost band of field value `v` of group `u`. -/
def band (u v : ℕ) : ℕ := bandIdx (A u) (nb u) v

/-- The slots of the block of field value `v` of group `u`. -/
def SL (u v : ℕ) : ℕ := if u = 11 then gap11 (pos11 v) else L u (band u v)

/-- The entry slot of field value `v` of group `u`. -/
def entryOf (u v : ℕ) : ℕ :=
  if u = 11 then BASE 11 + bd11 (pos11 v)
  else BASE u + OFF u (band u v) + (v - A u (band u v)) * L u (band u v)

/-- First free-chain entry, `sentinel − 68 · 96`. -/
def baseF : ℕ := 255615

/-- The sentinel slot `2 ^ 18 - 1`. -/
def sentinel : ℕ := 262143

/-- The free-chain entry of digit `s` (block length `s + 5 ≤ 68`). -/
def entF (s : ℕ) : ℕ := baseF + 68 * s

theorem baseF_add : baseF + 68 * 96 = sentinel := rfl

theorem A_mono (u : ℕ) : Monotone (A u) := fun a b h => by
  simpa only [A_eq] using psum_mono (pn u) h
theorem OFF_mono (u : ℕ) : Monotone (OFF u) := fun a b h => by
  simpa only [OFF_eq] using psum_mono (fun c => pn u c * L u c) h
theorem BASE_mono : Monotone BASE := fun a b h => by
  simpa only [BASE_eq] using Nat.add_le_add_left (psum_mono RS h) 27

theorem BASE_zero : BASE 0 = 27 := rfl

theorem BASE_succ (u : ℕ) : BASE (u + 1) = BASE u + RS u := by
  rw [BASE_eq, BASE_eq, psum_succ]; ring

theorem BASE_13 : BASE 13 = gEnd := by decide +kernel

theorem BASE_one : BASE 1 = 15869 := by decide

theorem A_full : ∀ u < 13, A u (nb u) = VF u := by decide

theorem VF_le : ∀ u < 13, VF u ≤ 2 ^ gb u := by decide

theorem nb_le : ∀ u < 13, nb u ≤ 18 := by decide

theorem nb_pos : ∀ u < 13, 1 ≤ nb u := by decide

theorem gcu_ge (u : ℕ) : 6 ≤ gcu u := by
  by_cases hu : u < 13
  · exact (show ∀ u < 13, 6 ≤ gcu u by decide) u hu
  · simp [gcu, List.getD_eq_default, show 13 ≤ u by omega]

theorem L_pos (u c : ℕ) : 5 ≤ L u c := by
  have hg := gcu_ge u
  unfold L
  omega

theorem OFF_succ (u c : ℕ) : OFF u (c + 1) = OFF u c + pn u c * L u c := by
  rw [OFF_eq, OFF_eq]; exact psum_succ _ c

theorem A_succ (u c : ℕ) : A u (c + 1) = A u c + pn u c := by
  rw [A_eq, A_eq]; exact psum_succ _ c

theorem gb_le : ∀ u < 13, gb u ≤ 12 := by decide

theorem POS_13 : POS 13 = 128 := by decide

theorem gk_le (u : ℕ) : gk u ≤ 4 := by unfold gk; split_ifs <;> omega

theorem gk_ge (u : ℕ) : 3 ≤ gk u := by unfold gk; split_ifs <;> omega

/-! ### Bands of field values -/

/-- The band of a field value and its position inside the band. -/
theorem band_spec {u v : ℕ} (hu : u < 13) (hv : v < VF u) :
    band u v < nb u ∧ A u (band u v) ≤ v ∧ v < A u (band u v + 1) := by
  have h := bandIdx_spec (A_mono u) (N := nb u) (o := v) (by rw [A_eq]; exact Nat.zero_le _)
    (by rw [A_full u hu]; exact hv)
  exact h

theorem band_lt_17 {u v : ℕ} (hu : u < 13) (hv : v < VF u) : band u v < 18 := by
  have := (band_spec hu hv).1; have := nb_le u hu; omega

theorem bd11_succ (j : ℕ) : bd11 (j + 1) = bd11 j + gap11 j := by
  rw [bd11_eq_slow, bd11_eq_slow]
  rfl

theorem bd11_mono : Monotone bd11 := monotone_nat_of_le_succ fun j => by rw [bd11_succ]; omega

theorem ord11_spec : ∀ j < 512, ord11 j < 512 ∧ pos11 (ord11 j) = j := by decide +kernel

theorem pos11_spec : ∀ v < 512, pos11 v < 512 ∧ ord11 (pos11 v) = v := by decide +kernel

theorem gap11_pos : ∀ j < 512, 5 ≤ gap11 j := by decide +kernel

theorem VF_11 : VF 11 = 512 := rfl

theorem SL_pos {u v : ℕ} (hu : u < 13) (hv : v < VF u) : 5 ≤ SL u v := by
  unfold SL
  split_ifs with h
  · subst h; exact gap11_pos _ (pos11_spec v hv).1
  · exact L_pos u _

theorem L_le_gap11 (v : ℕ) (hv : v < 512) : L 11 (band 11 v) ≤ gap11 (pos11 v) := by
  obtain ⟨hc, h1, h2⟩ := band_spec (u := 11) (by omega) (by rw [VF_11]; exact hv)
  rw [A_succ] at h2
  have hA : ∀ c < 18, A 11 c =
      [0, 0, 2, 7, 16, 30, 50, 77, 112, 156, 210, 275, 355, 445, 512, 512, 512, 512].getD c 0 := by
    decide +kernel
  have key : ∀ c < 18, ∀ i < pn 11 c, L 11 c ≤ gap11 (pos11 (A 11 c + i)) := by
    intro c hc
    rw [hA c hc]
    revert c
    decide +kernel
  have h := key (band 11 v) (by have := nb_le 11 (by omega); omega) (v - A 11 (band 11 v))
    (by omega)
  rwa [Nat.add_sub_cancel' h1] at h

/-- Every block holds its body and control op. -/
theorem L_le_SL {u v : ℕ} (hv : v < VF u) : L u (band u v) ≤ SL u v := by
  unfold SL
  split_ifs with h
  · subst h; exact L_le_gap11 v hv
  · exact le_rfl

/-- The block of field value `v` lies inside group `u`'s region. -/
theorem entry_region {u v i : ℕ} (hu : u < 13) (hv : v < VF u) (hi : i < SL u v) :
    BASE u ≤ entryOf u v + i ∧ entryOf u v + i < BASE (u + 1) := by
  rw [BASE_succ]
  by_cases h11 : u = 11
  · subst h11
    have hp := (pos11_spec v hv).1
    have hm := bd11_mono (show pos11 v + 1 ≤ 512 by omega)
    rw [bd11_succ] at hm
    simp only [SL, entryOf, RS, if_true] at hi ⊢
    omega
  · obtain ⟨hc, h1, h2⟩ := band_spec hu hv
    simp only [SL, entryOf, RS, if_neg h11] at hi ⊢
    set c := band u v
    have hq : v - A u c < pn u c := by rw [A_succ] at h2; omega
    have hoff : OFF u (c + 1) ≤ OFF u (nb u) := OFF_mono u (by omega)
    rw [OFF_succ] at hoff
    have hm : (v - A u c) * L u c + i < pn u c * L u c := by
      have : (v - A u c + 1) * L u c ≤ pn u c * L u c := Nat.mul_le_mul_right _ hq
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    omega

/-! ### The group decode -/

/-- Decode a group slot: the group, the field value and the offset in its block. -/
def dec (s : ℕ) : ℕ × ℕ × ℕ :=
  let u := bandIdx BASE 13 s
  let o := s - BASE u
  if u = 11 then
    let j := bandIdx bd11 512 o
    (11, ord11 j, o - bd11 j)
  else
    let c := bandIdx (OFF u) (nb u) o
    let q := o - OFF u c
    (u, A u c + q / L u c, q % L u c)

/-- Slots of a block decode to it. -/
theorem dec_entry {u v i : ℕ} (hu : u < 13) (hv : v < VF u) (hi : i < SL u v) :
    dec (entryOf u v + i) = (u, v, i) := by
  obtain ⟨hr1, hr2⟩ := entry_region hu hv hi
  have hU : bandIdx BASE 13 (entryOf u v + i) = u := bandIdx_eq BASE_mono hu hr1 hr2
  by_cases h11 : u = 11
  · subst h11
    obtain ⟨hp, hop⟩ := pos11_spec v hv
    simp only [SL, if_true] at hi
    have ho : entryOf 11 v + i - BASE 11 = bd11 (pos11 v) + i := by
      simp only [entryOf, if_true]; omega
    have hJ : bandIdx bd11 512 (bd11 (pos11 v) + i) = pos11 v :=
      bandIdx_eq bd11_mono hp (by omega) (by rw [bd11_succ]; omega)
    unfold dec
    simp only [hU, ↓reduceIte, ho, hJ, hop, Nat.add_sub_cancel_left]
  obtain ⟨hc, h1, h2⟩ := band_spec hu hv
  simp only [SL, if_neg h11] at hi
  set c := band u v with hcdef
  have hq : v - A u c < pn u c := by rw [A_succ] at h2; omega
  have hm : (v - A u c) * L u c + i < pn u c * L u c := by
    have : (v - A u c + 1) * L u c ≤ pn u c * L u c := Nat.mul_le_mul_right _ hq
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have ho : entryOf u v + i - BASE u = OFF u c + ((v - A u c) * L u c + i) := by
    unfold entryOf; rw [if_neg h11, ← hcdef]; omega
  have hC : bandIdx (OFF u) (nb u) (entryOf u v + i - BASE u) = c := by
    rw [ho]
    refine bandIdx_eq (OFF_mono u) hc (by omega) ?_
    rw [OFF_succ]; omega
  have hLp := L_pos u c
  unfold dec
  simp only [hU, if_neg h11]
  rw [hC, ho, Nat.add_sub_cancel_left]
  have hdiv : ((v - A u c) * L u c + i) / L u c = v - A u c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
  have hmod : ((v - A u c) * L u c + i) % L u c = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  rw [hdiv, hmod]
  congr 2
  omega

/-- Every group slot is a slot of a block of a field value in range. -/
theorem dec_spec {s : ℕ} (h1 : 27 ≤ s) (h2 : s < gEnd) :
    (dec s).1 < 13 ∧ (dec s).2.1 < VF (dec s).1 ∧
      (dec s).2.2 < SL (dec s).1 (dec s).2.1 ∧
      s = entryOf (dec s).1 (dec s).2.1 + (dec s).2.2 := by
  obtain ⟨hu, hb1, hb2⟩ := bandIdx_spec BASE_mono (N := 13) (o := s) (by rw [BASE_zero]; exact h1)
    (by rw [BASE_13]; exact h2)
  by_cases h11 : bandIdx BASE 13 s = 11
  · rw [h11] at hb1 hb2
    have hRS : s - BASE 11 < bd11 512 := by
      have := BASE_succ 11; simp only [RS, if_true] at this; omega
    obtain ⟨hj, hj1, hj2⟩ := bandIdx_spec bd11_mono (N := 512) (o := s - BASE 11)
      (Nat.zero_le _) hRS
    obtain ⟨ho, hpo⟩ := ord11_spec _ hj
    rw [bd11_succ] at hj2
    have hd : dec s = (11, ord11 (bandIdx bd11 512 (s - BASE 11)),
        s - BASE 11 - bd11 (bandIdx bd11 512 (s - BASE 11))) := by
      unfold dec; simp only [h11, ↓reduceIte]
    rw [hd]
    dsimp only
    refine ⟨by decide, ?_, ?_, ?_⟩
    · rw [VF_11]; exact ho
    · simp only [SL, if_true, hpo]; omega
    · simp only [entryOf, if_true, hpo]; omega
  set u := bandIdx BASE 13 s with hudef
  have hRS : s - BASE u < OFF u (nb u) := by
    have := BASE_succ u; simp only [RS, if_neg h11] at this; omega
  obtain ⟨hc, hc1, hc2⟩ := bandIdx_spec (OFF_mono u) (N := nb u) (o := s - BASE u)
    (by rw [OFF_eq]; exact Nat.zero_le _) hRS
  set c := bandIdx (OFF u) (nb u) (s - BASE u) with hcdef
  set q := s - BASE u - OFF u c with hqdef
  have hLp := L_pos u c
  rw [OFF_succ] at hc2
  have hqlt : q < pn u c * L u c := by omega
  have hj : q / L u c < pn u c := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; exact hqlt
  have hv1 : A u c ≤ A u c + q / L u c := Nat.le_add_right _ _
  have hv2 : A u c + q / L u c < A u (c + 1) := by rw [A_succ]; omega
  have hband : band u (A u c + q / L u c) = c := bandIdx_eq (A_mono u) hc hv1 hv2
  have hvlt : A u c + q / L u c < VF u := by
    have := A_mono u (show c + 1 ≤ nb u by omega)
    rw [A_full u hu] at this; omega
  have hd : dec s = (u, A u c + q / L u c, q % L u c) := by
    unfold dec; simp only [← hudef, if_neg h11]; rfl
  rw [hd]
  refine ⟨hu, hvlt, ?_, ?_⟩
  · simp only [SL, if_neg h11]; rw [hband]; exact Nat.mod_lt _ (by omega)
  · simp only [entryOf, if_neg h11]
    rw [hband, Nat.add_sub_cancel_left]
    have := Nat.div_add_mod q (L u c)
    rw [mul_comm] at this
    omega

/-- Distinct field values have distinct entries. -/
theorem entryOf_inj {u v v' : ℕ} (hu : u < 13) (hv : v < VF u) (hv' : v' < VF u)
    (h : entryOf u v = entryOf u v') : v = v' := by
  have h1 := dec_entry hu hv (i := 0) (by have := SL_pos hu hv; omega)
  have h2 := dec_entry hu hv' (i := 0) (by have := SL_pos hu hv'; omega)
  rw [Nat.add_zero] at h1 h2
  rw [h] at h1
  rw [h1] at h2
  exact (Prod.mk.inj (Prod.mk.inj h2).2).1

theorem entryOf_ge {u v : ℕ} (hu : u < 13) (hv : v < VF u) : 27 ≤ entryOf u v := by
  have := (entry_region hu hv (i := 0) (by have := SL_pos hu hv; omega)).1
  have := BASE_mono (Nat.zero_le u); rw [BASE_zero] at this; omega

theorem block_lt_gEnd {u v i : ℕ} (hu : u < 13) (hv : v < VF u) (hi : i < SL u v) :
    entryOf u v + i < gEnd := by
  have := (entry_region hu hv hi).2
  have := BASE_mono (show u + 1 ≤ 13 by omega); rw [BASE_13] at this; omega

/-! ## Chains -/

/-- Chain lengths (positions), from the tables' maximal coordinates. -/
def LENL : List ℕ := [64, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17]

/-- Positions of chain `k`. -/
def LEN (k : ℕ) : ℕ := LENL.getD k 0

/-- First tag position of chain `k`: steps are numbered consecutively over the chains. -/
def OFFT (k : ℕ) : ℕ := psum (fun j => LEN j - 1) k

/-- First scratch cell of chain `k`. -/
def xcBase (k : ℕ) : ℕ := 4096 + 2 * psum LEN k

theorem LEN_le : ∀ k < 42, LEN k ≤ 64 := by decide

theorem LEN_pos : ∀ k < 42, 2 ≤ LEN k := by decide

theorem OFFT_bound : ∀ k < 42, OFFT k + LEN k ≤ 720 := by decide

theorem xcBase_bound : ∀ k < 42, xcBase k + 2 * LEN k ≤ 5618 := by decide

theorem xcBase_mono : Monotone xcBase := fun _ _ h =>
  Nat.add_le_add_left (Nat.mul_le_mul_left 2 (psum_mono LEN h)) 4096

theorem xcBase_succ (k : ℕ) : xcBase (k + 1) = xcBase k + 2 * LEN k := by
  unfold xcBase; rw [psum_succ]; ring

theorem xcBase_42 : xcBase 42 = 5618 := by decide

theorem xcBase_zero : xcBase 0 = 4096 := rfl

/-- The thirteen decoding groups; group 5 is the single root-message home. -/
def chainOf (u i : ℕ) : ℕ := ([[1, 2, 7], [12, 13, 17], [18, 22, 23], [27, 28, 32], [33, 37, 38], [3, 4, 5, 6], [8, 9, 10, 11], [14, 15, 16], [19, 20, 21], [24, 25, 26], [29, 30, 31], [34, 35, 36], [39, 40, 41]].getD u []).getD i 0

def unitOf (k : ℕ) : ℕ := [0, 0, 0, 5, 5, 5, 5, 0, 6, 6, 6, 6, 1, 1, 7, 7, 7, 1, 2, 8, 8, 8, 2, 2, 9, 9, 9, 3, 3, 10, 10, 10, 3, 4, 11, 11, 11, 4, 4, 12, 12, 12].getD k 0

def coordOf (k : ℕ) : ℕ := [0, 0, 1, 0, 1, 2, 3, 2, 0, 1, 2, 3, 0, 1, 0, 1, 2, 2, 0, 0, 1, 2, 1, 2, 0, 1, 2, 0, 1, 0, 1, 2, 2, 0, 0, 1, 2, 1, 2, 0, 1, 2].getD k 0

/-- Tops always materialized at `topCell`. The others are root-call messages, which read the
revealed word when their digit is zero. -/
def visible (u : ℕ) : ℕ := gk u - (if u = 6 then 2 else if u = 11 ∨ u = 12 then 1 else 0)
def copied (u i : ℕ) : Prop := isExp u ∧ i < visible u
instance (u i : ℕ) : Decidable (copied u i) := by unfold copied; infer_instance

def exported (k : ℕ) : Prop := k ∉ [3,4,5,6,10,11,36,41]

instance (k : ℕ) : Decidable (exported k) := by unfold exported; infer_instance

theorem chainOf_lt : ∀ u < 13, ∀ i < gk u, chainOf u i < 42 := by decide

theorem chainOf_pos : ∀ u < 13, ∀ i < gk u, 1 ≤ chainOf u i := by decide

theorem unitOf_chainOf : ∀ u < 13, ∀ i < gk u, unitOf (chainOf u i) = u := by decide

theorem coordOf_chainOf : ∀ u < 13, ∀ i < gk u, coordOf (chainOf u i) = i := by decide

theorem chainOf_unitOf : ∀ k < 42, 1 ≤ k →
    unitOf k < 13 ∧ coordOf k < gk (unitOf k) ∧ chainOf (unitOf k) (coordOf k) = k := by decide

theorem exported_iff : ∀ u < 13, ∀ i < gk u, (exported (chainOf u i) ↔ copied u i) := by decide

/-! ## Values -/

/-- The constant `1`. -/
def oneV : E := ofK 1

/-- The generator `g`. -/
def gV : E := ofK g

/-- The cost constant `C_c = g ^ (2^60 * c)`, also the tag symbol `c`. -/
def cV (c : ℕ) : E := ofK (gpow (1152921504606846976 * c))

/-- Upper bound on the fourteen frame exponents. -/
def eLen : ℕ := 17293822569102704640

/-- Fourteen frames reuse C1..C13 and the validated length word. -/
def frameExp (f : ℕ) : ℕ :=
  if f = 0 then 1152921504606846976
  else if f = 1 then 1434881718044321323
  else f * 1152921504606846976

/-- The frame pointer of frame `f`. -/
def frame (f : ℕ) : K := gpow (frameExp f)

/-- The frame constant of frame `f`; `frameV r` is also the metadata of root call `r`. -/
def frameV (f : ℕ) : E := ofK (frame f)

/-- The tie pattern of field value `v` of group `u`: the field layout rotated left by 47 bits,
so that unit 11's field lands on the bits its landing hint carries (`IndexBits`). -/
def fpat (u v : ℕ) : E := cellOfBits ((BitVec.ofNat 128 (v * 2 ^ POS u)).rotateLeft 47)

theorem cV_zero : cV 0 = oneV := by unfold cV oneV; rw [Nat.mul_zero, gpow_zero']

theorem cV_sixteen : cV 16 = gV := by
  exact congrArg ofK LeanIsaFieldRescale.factor_sixteen

theorem frameV_eq_cV {f : ℕ} (hf : f ≠ 1) :
    frameV f = cV (if f = 0 then 1 else f) := by
  unfold frameV frame frameExp cV
  split_ifs <;> first | (exfalso; omega) | (congr 2 <;> omega)

theorem frameV_one : frameV 1 = OptimalOTS.HLG3.natV 5504 := by
  change ofK (gpow 1434881718044321323) = ofK (BitVec.ofNat 64 5504)
  rw [OptimalOTS.HLG3.LengthGate.log5504]
  rfl

/-- Frame exponents are far apart and far from `0` modulo the order of `g`. -/
theorem frameExp_bounds {f : ℕ} (hf : f < 14) :
    2 ^ 33 ≤ frameExp f ∧ frameExp f ≤ eLen := by
  exact (show ∀ f < 14, 2 ^ 33 ≤ frameExp f ∧ frameExp f ≤ eLen by decide) f hf

theorem frameExp_sep {f j : ℕ} (hf : f < 14) (hj : j < 14) (h : j < f) :
    frameExp j + 2 ^ 33 ≤ frameExp f := by
  exact (show ∀ f < 14, ∀ j < 14, j < f → frameExp j + 2 ^ 33 ≤ frameExp f by decide) f hf j hj h

/-! ## The table and scheme interfaces -/

/-- A group table: coordinate `i` of the tuple of field value `v` of group `u`. -/
abbrev Tab := ℕ → ℕ → ℕ → ℕ

/-- The cost (coordinate sum) of the tuple of field value `v` of group `u`. -/
def cost (T : Tab) (u v : ℕ) : ℕ := ((List.range (gk u)).map (T u v)).sum

/-- Visible coordinates are materialized; internal message children are read in place. -/
def bindingDeduction (u : ℕ) : ℕ := if (1 ≤ u ∧ u ≤ 4) ∨ u = 7 then 0 else 1
def copyCount (T : Tab) (u v : ℕ) : ℕ :=
  ((List.range (gk u)).map (fun i => if copied u i ∧ T u v i = 0 then 1 else 0)).sum
def machineOrdinary (T : Tab) (u v : ℕ) : ℕ :=
  (if u ≠ 0 ∧ u ≠ 11 ∧ v ≠ 0 then 2 else 1) + copyCount T u v + 3 +
    (if 14 < cost T u v - bindingDeduction u then 1 else 0)

theorem packed_group_budget : (∑ u ∈ Finset.range 13, (gcu u - 1)) = 84 := by decide

theorem packed_raw_blocks : (∑ u ∈ Finset.range 13, VF u) = 14820 := by decide

theorem packed_double_mul_blocks :
    (∑ u ∈ Finset.range 13, ∑ c ∈ Finset.range 18,
      if 14 < c - bindingDeduction u then pn u c else 0) = 845 := by decide

theorem table7_live : VF 7 = 996 := rfl

/-- What the machine needs of the tables: the cost of a live tuple is its cost band, and every
coordinate is below its chain's length. -/
structure Tab.Hyp (T : Tab) : Prop where
  cost_eq : ∀ u < 13, ∀ v < VF u, cost T u v = band u v
  coord_lt : ∀ u < 13, ∀ v < 2 ^ gb u, ∀ i < gk u, T u v i < LEN (chainOf u i)
  ordinary_le : ∀ u < 13, ∀ v < VF u, machineOrdinary T u v ≤ gcu u - 1

/-- The free chain's digit: `85 − c` for group cost `c` when that is in `[0, 63]`, else `0`. -/
def freeDigit (c : ℕ) : ℕ := if c ≤ 85 ∧ 85 - c ≤ 63 then 85 - c else 0

/-- Group `u`'s field of the index, read after removing unit 11's hint mask. -/
def field (u : ℕ) (I : Word) : ℕ := digitW gb (unmask I).toNat u

/-- The total group cost of an index. -/
def gcost (T : Tab) (I : Word) : ℕ := ((List.range 13).map (fun u => cost T u (field u I))).sum

end OptimalOTS.HLFour
