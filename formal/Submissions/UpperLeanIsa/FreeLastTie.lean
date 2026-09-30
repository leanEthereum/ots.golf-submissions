import Submissions.UpperLeanIsa.FreeLastPath
import Submissions.UpperLeanIsa.HintTie

namespace OptimalOTS.FreeLastTie
open LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.LeanIsaBaseline.Layer OptimalOTS.PartialHints
open OptimalOTS.LeanIsa (cellBits cellOfBits)
open OptimalOTS.HLG3 (cellOfBits_add)
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

 theorem permutation_bit (x : BitVec 128) (i : Fin 128) :
    (wordPermutation x).getLsbD i.val = x.getLsbD (bitBackward i).val := by
  change wordBitsEquiv (wordBitsEquiv.symm
    ((Equiv.arrowCongr bitEquiv (Equiv.refl Bool)) (wordBitsEquiv x))) i = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem permutation_xor (x y : BitVec 128) :
    wordPermutation (x ^^^ y) = wordPermutation x ^^^ wordPermutation y := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_xor]
  rw [permutation_bit _ ⟨i,hi⟩,permutation_bit _ ⟨i,hi⟩,permutation_bit _ ⟨i,hi⟩,
    BitVec.getLsbD_xor]

theorem permutation_zero : wordPermutation 0 = 0 := by
  ext i hi
  rw [← BitVec.getLsbD_eq_getElem,← BitVec.getLsbD_eq_getElem,permutation_bit _ ⟨i,hi⟩]
  simp

theorem selector11_permutation (x : BitVec 128) :
    hintField (wordPermutation x) = x.extractLsb' 109 9 := by
  ext i hi
  simp only [hintField,← BitVec.getLsbD_eq_getElem,BitVec.getLsbD_extractLsb']
  simp only [hi,decide_true,Bool.true_and]
  rw [permutation_bit _ ⟨28+i,by omega⟩]
  congr 1
  interval_cases i <;> rfl

theorem selector8_permutation (x : BitVec 128) :
    selector8 (wordPermutation x) = field8 x := by
  ext i hi
  simp only [selector8,field8,← BitVec.getLsbD_eq_getElem,
    BitVec.getLsbD_append,BitVec.getLsbD_extractLsb']
  interval_cases i
  all_goals simp only [Nat.reduceLT,decide_true,decide_false,Bool.true_and,Bool.false_and,ite_true,ite_false,Nat.reduceAdd,Nat.reduceSub]
  all_goals rw [permutation_bit _ ⟨_,by decide⟩]
  all_goals rfl

theorem selector9_permutation (x : BitVec 128) :
    selector9 (wordPermutation x) = field9 x := by
  ext i hi
  simp only [selector9,field9,← BitVec.getLsbD_eq_getElem,BitVec.getLsbD_extractLsb']
  simp only [hi,decide_true,Bool.true_and,Nat.zero_add]
  rw [permutation_bit _ ⟨i,by omega⟩]
  congr 1
  interval_cases i <;> rfl

def pack (xs : Nat → Nat) : BitVec 128 := BitVec.ofNat 128 (ofDigitsW gb xs 13)
def labels (xs : Nat → Nat) (u : Nat) : Nat := FreeLastBlocks.label u (xs u)

theorem label_bound (xs : Nat → Nat) (hx : ∀ u, xs u < 2^gb u) :
    ∀ u, labels xs u < 2^gb u := by
  intro u
  unfold labels FreeLastBlocks.label
  split_ifs with h8 h9
  · subst u; exact (label8Inv _).isLt
  · subst u; exact (label9Inv _).isLt
  · exact hx u

theorem extract_digit (x : BitVec 128) (u : Nat) :
    (x.extractLsb' (POS u) (gb u)).toNat = digitW gb x.toNat u := by
  rw [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  rfl

theorem pack_digit (xs : Nat → Nat) (hx : ∀ u, xs u < 2^gb u)
    {u : Nat} (hu : u < 13) : digitW gb (pack xs).toNat u = xs u := by
  have hh := ofDigitsW_lt gb xs hx 13
  rw [show posW gb 13 = 128 from POS_13] at hh
  rw [pack,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hh,digitW_ofDigitsW gb xs hx 13 u hu]

theorem word_digits_ext (x y : BitVec 128)
    (h : ∀ u < 13, digitW gb x.toNat u = digitW gb y.toNat u) : x = y := by
  apply BitVec.eq_of_toNat_eq
  have hx : x.toNat < 2^posW gb 13 := by change x.toNat < 2^128; exact x.isLt
  have hy : y.toNat < 2^posW gb 13 := by change y.toNat < 2^128; exact y.isLt
  rw [← ofDigitsW_digitW gb _ 13 hx,← ofDigitsW_digitW gb _ 13 hy]
  unfold ofDigitsW
  apply Finset.sum_congr rfl
  intro u hu
  rw [h u (Finset.mem_range.mp hu)]

theorem extract_extract {w : Nat} (x : BitVec w) (a b c d : Nat) (h : c+d ≤ b) :
    (x.extractLsb' a b).extractLsb' c d = x.extractLsb' (a+c) d := by
  ext i hi
  have hci : c+i < b := by omega
  simp only [← BitVec.getLsbD_eq_getElem,BitVec.getLsbD_extractLsb',
    hi,hci,decide_true,Bool.true_and,Nat.add_assoc]

theorem extract_replace_low {n a b c start len : Nat} (x : BitVec n) (v : BitVec b)
    (h : start+len ≤ a) :
    ((x.extractLsb' (a+b) c ++ v) ++ x.extractLsb' 0 a).extractLsb' start len =
      x.extractLsb' start len := by
  rw [BitVec.extractLsb'_append_eq_of_add_le h,extract_extract _ _ _ _ _ h,Nat.zero_add]

theorem extract_replace_high {n a b c start len : Nat} (x : BitVec n) (v : BitVec b)
    (h : a+b ≤ start) (hhi : start+len ≤ a+b+c) :
    ((x.extractLsb' (a+b) c ++ v) ++ x.extractLsb' 0 a).extractLsb' start len =
      x.extractLsb' start len := by
  rw [BitVec.extractLsb'_append_eq_of_le (by omega : a ≤ start),
    BitVec.extractLsb'_append_eq_of_le (by omega : b ≤ start-a),
    extract_extract _ _ _ _ _ (by omega)]
  rw [show a+b+(start-a-b) = start by omega]

theorem replace8_digit (x : BitVec 128) (v : BitVec 10) {u : Nat} (hu : u < 13) :
    digitW gb (replace8 x v).toNat u = if u = 8 then v.toNat else digitW gb x.toNat u := by
  rw [← extract_digit,← extract_digit]
  by_cases h8 : u = 8
  · subst u; exact congrArg BitVec.toNat (field8_replace x v)
  rw [if_neg h8]
  have hr : POS u+gb u ≤ 79 ∨ 89 ≤ POS u ∧ POS u+gb u ≤ 128 :=
    (show ∀ u < 13, u ≠ 8 → POS u+gb u ≤ 79 ∨ 89 ≤ POS u ∧ POS u+gb u ≤ 128 by decide) u hu h8
  congr 1
  rcases hr with hl | hh
  · exact extract_replace_low x v hl
  · exact extract_replace_high x v hh.1 hh.2

theorem replace9_digit (x : BitVec 128) (v : BitVec 10) {u : Nat} (hu : u < 13) :
    digitW gb (replace9 x v).toNat u = if u = 9 then v.toNat else digitW gb x.toNat u := by
  rw [← extract_digit,← extract_digit]
  by_cases h9 : u = 9
  · subst u; exact congrArg BitVec.toNat (field9_replace x v)
  rw [if_neg h9]
  have hr : POS u+gb u ≤ 89 ∨ 99 ≤ POS u ∧ POS u+gb u ≤ 128 :=
    (show ∀ u < 13, u ≠ 9 → POS u+gb u ≤ 89 ∨ 99 ≤ POS u ∧ POS u+gb u ≤ 128 by decide) u hu h9
  congr 1
  rcases hr with hl | hh
  · exact extract_replace_low x v hl
  · exact extract_replace_high x v hh.1 hh.2

theorem field8_pack (xs : Nat → Nat) (hx : ∀ u, xs u < 2^gb u) :
    field8 (pack xs) = BitVec.ofNat 10 (xs 8) := by
  apply BitVec.eq_of_toNat_eq
  have hh : xs 8 < 2^10 := hx 8
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hh]
  exact (extract_digit (pack xs) 8).trans (pack_digit xs hx (by decide))

theorem field9_pack (xs : Nat → Nat) (hx : ∀ u, xs u < 2^gb u) :
    field9 (pack xs) = BitVec.ofNat 10 (xs 9) := by
  apply BitVec.eq_of_toNat_eq
  have hh : xs 9 < 2^10 := hx 9
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hh]
  exact (extract_digit (pack xs) 9).trans (pack_digit xs hx (by decide))

theorem field9_replace8 (x : BitVec 128) (v : BitVec 10) :
    field9 (replace8 x v) = field9 x := by
  apply BitVec.eq_of_toNat_eq
  exact (extract_digit (replace8 x v) 9).trans
    ((replace8_digit x v (u:=9) (by decide)).trans (extract_digit x 9).symm)

theorem pack_labels (xs : Nat → Nat) (hx : ∀ u, xs u < 2^gb u) :
    replace9 (replace8 (pack xs) (label8Inv (field8 (pack xs))))
      (label9Inv (field9 (replace8 (pack xs) (label8Inv (field8 (pack xs)))))) =
        pack (labels xs) := by
  rw [field9_replace8,field8_pack xs hx,field9_pack xs hx]
  apply word_digits_ext
  intro u hu
  rw [replace9_digit _ _ hu,replace8_digit _ _ hu,pack_digit xs hx hu,
    pack_digit (labels xs) (label_bound xs hx) hu]
  unfold labels FreeLastBlocks.label
  by_cases h8 : u = 8
  · subst u; rfl
  · by_cases h9 : u = 9
    · subst u; rfl
    · simp only [if_neg h9,if_neg h8]

theorem encode_pack (xs : Nat → Nat) (hx : ∀ u, xs u < 2^gb u) :
    encodeRaw (pack xs) = wordPermutation (pack (labels xs)) ^^^ hintMask (xs 11) ^^^
      mask8 (labels xs 8) ^^^ mask9 (labels xs 9) := by
  change hintEquiv (wordPermutation
    (replace9 (replace8 (pack xs) (label8Inv (field8 (pack xs))))
      (label9Inv (field9 (replace8 (pack xs) (label8Inv (field8 (pack xs)))))))) = _
  rw [pack_labels xs hx,hintEquiv_apply,selector11_permutation,selector8_permutation,selector9_permutation]
  have h11 : ((pack (labels xs)).extractLsb' 109 9).toNat = xs 11 :=
    (extract_digit (pack (labels xs)) 11).trans (pack_digit (labels xs) (label_bound xs hx) (by decide))
  have h8 : (field8 (pack (labels xs))).toNat = labels xs 8 :=
    (extract_digit (pack (labels xs)) 8).trans (pack_digit (labels xs) (label_bound xs hx) (by decide))
  have h9 : (field9 (pack (labels xs))).toNat = labels xs 9 :=
    (extract_digit (pack (labels xs)) 9).trans (pack_digit (labels xs) (label_bound xs hx) (by decide))
  rw [h11,h8,h9]

def mask (u v : Nat) : BitVec 128 :=
  if u = 8 then mask8 (FreeLastBlocks.label u v)
  else if u = 9 then mask9 (FreeLastBlocks.label u v)
  else if u = 11 then hintMask v else 0

def part (u v : Nat) : BitVec 128 :=
  wordPermutation (BitVec.ofNat 128 (FreeLastBlocks.label u v * 2^POS u)) ^^^ mask u v

def accBits (xs : Nat → Nat) (u : Nat) : BitVec 128 :=
  wordPermutation (BitVec.ofNat 128 (ofDigitsW gb (labels xs) (u+1))) ^^^
    (if 8 ≤ u then mask8 (labels xs 8) else 0) ^^^
    (if 9 ≤ u then mask9 (labels xs 9) else 0) ^^^
    (if 11 ≤ u then hintMask (xs 11) else 0)

theorem xor_zero (x : BitVec 128) : x ^^^ (0 : BitVec 128) = x := BitVec.xor_zero
theorem zero_xor (x : BitVec 128) : (0 : BitVec 128) ^^^ x = x := BitVec.zero_xor

theorem xor_four_shuffle (a b c d : BitVec 128) :
    a ^^^ b ^^^ c ^^^ d = a ^^^ d ^^^ b ^^^ c := by
  ac_rfl

theorem acc_zero (xs : Nat → Nat) (hx : ∀ u, xs u < 2^gb u) :
    accBits xs 0 = part 0 (xs 0) := by
  unfold accBits part mask
  rw [ofNat_digits_succ (label_bound xs hx) (by decide : 0 < 13),ofDigitsW_zero,permutation_xor]
  have hz : wordPermutation (BitVec.ofNat 128 0) = (0 : BitVec 128) := permutation_zero
  rw [hz]
  simp only [show ¬(8 ≤ 0) by decide,show ¬(9 ≤ 0) by decide,show ¬(11 ≤ 0) by decide,
    show ¬((0 : Nat) = 8) by decide,show ¬((0 : Nat) = 9) by decide,show ¬((0 : Nat) = 11) by decide,
    if_false,zero_xor,xor_zero,labels]

theorem mask_step (u : Nat) (hu : u < 12) (a b c x y : BitVec 128) :
    (((x ^^^ (if 8 ≤ u then a else 0#128)) ^^^ (if 9 ≤ u then b else 0#128)) ^^^
      (if 11 ≤ u then c else 0#128)) ^^^
        (y ^^^ (if u+1 = 8 then a else if u+1 = 9 then b else if u+1 = 11 then c else 0#128)) =
    (((x ^^^ y ^^^ (if 8 ≤ u+1 then a else 0#128)) ^^^ (if 9 ≤ u+1 then b else 0#128)) ^^^
      (if 11 ≤ u+1 then c else 0#128)) := by
  interval_cases u <;> norm_num <;> ac_rfl

theorem acc_step (xs : Nat → Nat) (hx : ∀ u, xs u < 2^gb u)
    {u : Nat} (hu : u+1 < 13) : accBits xs u ^^^ part (u+1) (xs (u+1)) = accBits xs (u+1) := by
  unfold accBits part
  rw [ofNat_digits_succ (label_bound xs hx) hu,permutation_xor]
  have hm : mask (u+1) (xs (u+1)) =
      if u+1 = 8 then mask8 (labels xs 8) else if u+1 = 9 then mask9 (labels xs 9)
      else if u+1 = 11 then hintMask (xs 11) else 0#128 := by
    unfold mask
    split_ifs with h8 h9 h11
    · rw [h8]; rfl
    · rw [h9]; rfl
    · rw [h11]
    · rfl
  rw [hm]
  exact mask_step u (by omega) _ _ _ _ _

theorem acc_encode (xs : Nat → Nat) (hx : ∀ u, xs u < 2^gb u) :
    accBits xs 12 = encodeRaw (pack xs) := by
  rw [encode_pack xs hx]
  unfold accBits
  rw [if_pos (by decide : 8 ≤ 12),if_pos (by decide : 9 ≤ 12),if_pos (by decide : 11 ≤ 12)]
  exact xor_four_shuffle (wordPermutation (pack (labels xs)))
    (mask8 (labels xs 8)) (mask9 (labels xs 9)) (hintMask (xs 11))

theorem piece_bit {v w i : Nat} (hv : v < 2^w) (hi : i < 128) (p : Nat) :
    (BitVec.ofNat 128 (v*2^p)).getLsbD i =
      if p ≤ i ∧ i < p+w then v.testBit (i-p) else false := by
  rw [BitVec.getLsbD_ofNat,Nat.testBit_mul_two_pow]
  by_cases hp : p ≤ i
  · by_cases hw : i < p+w
    · simp [hi,hp,hw]
    · have hz : v.testBit (i-p) = false := Nat.testBit_lt_two_pow
        (hv.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hi,hp,hw,hz]
  · simp [hi,hp]

def PieceMap (p q w : Nat) : Prop := ∀ i : Fin 128,
  (p ≤ (bitBackward i).val ∧ (bitBackward i).val < p+w ↔ q ≤ i.val ∧ i.val < q+w) ∧
  (q ≤ i.val ∧ i.val < q+w → (bitBackward i).val-p = i.val-q)
instance (p q w : Nat) : Decidable (PieceMap p q w) := inferInstanceAs (Decidable (∀ i : Fin 128, _))

theorem permutation_piece {p q w v : Nat} (hm : PieceMap p q w) (hv : v < 2^w) :
    wordPermutation (BitVec.ofNat 128 (v*2^p)) = BitVec.ofNat 128 (v*2^q) := by
  ext i hi
  rw [← BitVec.getLsbD_eq_getElem,← BitVec.getLsbD_eq_getElem,permutation_bit _ ⟨i,hi⟩,
    piece_bit hv (bitBackward ⟨i,hi⟩).isLt, piece_bit hv hi]
  have hh := hm ⟨i,hi⟩
  by_cases h : q ≤ i ∧ i < q+w
  · rw [if_pos (hh.1.mpr h),if_pos h,hh.2 h]
  · rw [if_neg (fun hp => h (hh.1.mp hp)),if_neg h]


theorem pattern8_checked : ∀ v : Fin 64,
    wordPermutation (BitVec.ofNat 128 (v.val*2^79)) = BitVec.ofNat 128 (v.val*2^37) := by
  intro v
  exact permutation_piece (w:=6) (by decide +kernel : PieceMap 79 37 6) v.isLt

theorem pattern9_checked : ∀ v : BitVec 10,
    wordPermutation (BitVec.ofNat 128 (v.toNat*2^89)) = BitVec.ofNat 128 v.toNat := by
  intro v
  exact (permutation_piece (w:=10) (by decide +kernel : PieceMap 89 0 10) v.isLt).trans
    (by rw [pow_zero,Nat.mul_one])

theorem pattern11_checked : ∀ v : BitVec 9,
    wordPermutation (BitVec.ofNat 128 (v.toNat*2^109)) = BitVec.ofNat 128 (v.toNat*2^28) := by
  intro v
  exact permutation_piece (w:=9) (by decide +kernel : PieceMap 109 28 9) v.isLt

theorem mask8_unhinted : ∀ v < 1024, hinted8 v = false →
    mask8 (label8Inv (BitVec.ofNat 10 v)).toNat = 0 := by decide +kernel

theorem mask9_unhinted : ∀ v < 1024, hinted9 v = false →
    mask9 (label9Inv (BitVec.ofNat 10 v)).toNat = 0 := by decide +kernel

theorem label8_inv_nat {l v : Nat} (hl : l < 1024)
    (h : (label8 (BitVec.ofNat 10 l)).toNat = v) : FreeLastBlocks.label 8 v = l := by
  change (label8Inv (BitVec.ofNat 10 v)).toNat = l
  rw [← h,BitVec.ofNat_toNat,BitVec.setWidth_eq,label8_left,BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hl

theorem label9_inv_nat {l v : Nat} (hl : l < 1024)
    (h : (label9 (BitVec.ofNat 10 l)).toNat = v) : FreeLastBlocks.label 9 v = l := by
  change (label9Inv (BitVec.ofNat 10 v)).toNat = l
  rw [← h,BitVec.ofNat_toNat,BitVec.setWidth_eq,label9_left,BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hl

theorem hint8_value {e v : Nat} (h : FreeLastLayout.hintAt 8 v e = true) :
    FreeLastBlocks.label 8 v < 64 ∧
    (gpow e).toNat = Nat.xor (mask8V (FreeLastBlocks.label 8 v)) (FreeLastBlocks.label 8 v*2^37) := by
  change hints8.any (fun r => r.1 == e && (label8 (BitVec.ofNat 10 r.2.1)).toNat == v) = true at h
  obtain ⟨r,hr,h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true,beq_iff_eq] at h
  have hc := List.all_eq_true.mp hints8_checked r hr
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hc
  have hl := label8_inv_nat (by omega : r.2.1 < 1024) h.2
  rw [hl,← h.1]
  exact ⟨hc.1.1.2,(GenFast.pow_toNat g 18 r.1 hc.1.1.1).trans (hc.1.2.trans hc.2)⟩

theorem hint9_value {e v : Nat} (h : FreeLastLayout.hintAt 9 v e = true) :
    FreeLastBlocks.label 9 v < 1024 ∧
    (gpow e).toNat = Nat.xor (mask9V (FreeLastBlocks.label 9 v)) (FreeLastBlocks.label 9 v) := by
  change hints9.any (fun r => r.1 == e && (label9 (BitVec.ofNat 10 r.2.1)).toNat == v) = true at h
  obtain ⟨r,hr,h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true,beq_iff_eq] at h
  have hc := List.all_eq_true.mp hints9_checked r hr
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hc
  have hl := label9_inv_nat hc.1.1.2 h.2
  rw [hl,← h.1]
  exact ⟨hc.1.1.2,(GenFast.pow_toNat g 18 r.1 hc.1.1.1).trans (hc.1.2.trans hc.2)⟩

theorem ofNat_natXor (a b : Nat) :
    BitVec.ofNat 128 (Nat.xor a b) = BitVec.ofNat 128 a ^^^ BitVec.ofNat 128 b :=
  BitVec.ofNat_xor

theorem landing_part {mem : Nat → E} {u v : Nat} {z : Bool}
    (hl : FreeLastVM.GroupLanding mem u v z) (hh : FreeLastBlocks.hinted u v = true) :
    mem (hCell (u+1)) = cellOfBits (part u v) := by
  obtain ⟨e,he,hehi,hm,hb,hentry⟩ := hl
  have hg := (FreeLastLayout.candidate_lookup_good he hehi).1.2
  simp only [hb] at hg
  have hat := hg.2.2.2.2.2.1 hh
  rw [hentry] at hat
  rw [hm,ofK_eq_cellOfBits]
  congr 1
  by_cases h8 : u = 8
  · subst u
    obtain ⟨hl8,he8⟩ := hint8_value hat
    rw [he8,ofNat_natXor]
    have hp := pattern8_checked ⟨FreeLastBlocks.label 8 v,hl8⟩
    unfold part
    rw [show POS 8 = 79 from rfl,hp]
    exact BitVec.xor_comm _ _
  by_cases h9 : u = 9
  · subst u
    obtain ⟨hl9,he9⟩ := hint9_value hat
    rw [he9,ofNat_natXor]
    have hp := pattern9_checked (BitVec.ofNat 10 (FreeLastBlocks.label 9 v))
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hl9] at hp
    unfold part
    rw [show POS 9 = 89 from rfl,hp]
    exact BitVec.xor_comm _ _
  have h11 : u = 11 := by
    by_contra hn
    simp only [FreeLastBlocks.hinted,if_neg hn,if_neg h8,if_neg h9] at hh
    cases hh
  subst u
  have he11 := (hg.2.2.2.2.1 (Or.inl rfl)).1
  rw [hentry] at he11
  have hv : v < 512 := hg.2.1
  rw [he11,gpow_entry11 hv,ofNat_natXor]
  have hp := pattern11_checked (BitVec.ofNat 9 v)
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hv] at hp
  unfold part
  rw [show FreeLastBlocks.label 11 v = v from rfl,show POS 11 = 109 from rfl,hp]
  exact BitVec.xor_comm _ _

theorem mask_unhinted {u v : Nat} (hu : u < 13) (hv : v < VF u)
    (hh : FreeLastBlocks.hinted u v = false) : mask u v = 0 := by
  by_cases h8 : u = 8
  · subst u; exact mask8_unhinted v hv hh
  by_cases h9 : u = 9
  · subst u; exact mask9_unhinted v hv hh
  have h11 : u ≠ 11 := by intro h; subst u; cases hh
  simp only [mask,if_neg h8,if_neg h9,if_neg h11]

theorem pattern_zero (u : Nat) : FreeLastBlocks.pattern u 0 = 0 := by
  have hl : FreeLastBlocks.label u 0 = 0 := by
    unfold FreeLastBlocks.label
    split_ifs <;> decide
  rw [FreeLastBlocks.pattern,hl,Nat.zero_mul,show BitVec.ofNat 128 0 = 0 from rfl,permutation_zero]
  exact OptimalOTS.HLG3.cellOfBits_zero

theorem part_plain {u v : Nat} (hu : u < 13) (hv : v < VF u)
    (hh : FreeLastBlocks.hinted u v = false) : cellOfBits (part u v) = FreeLastBlocks.pattern u v := by
  rw [part,mask_unhinted hu hv hh,xor_zero]
  rfl

theorem tie_first {B : BlakeRel} {mem : Nat → E} {xs : Nat → Nat} {s : Nat} {z : Bool}
    (hp : FreeLastVM.PathFacts B mem xs s z) : mem (accCell 0) = cellOfBits (part 0 (xs 0)) := by
  have h := hp.tie_rel (u:=0) (by decide) (ci:=.setc (accCell 0) (FreeLastBlocks.pattern 0 (xs 0)))
    (by simp only [FreeLastBlocks.tie,if_true,List.mem_singleton])
  change mem (accCell 0) = FreeLastBlocks.pattern 0 (xs 0) at h
  rw [part_plain (by decide : 0 < 13) (hp.valid 0 (by decide)) rfl]
  exact h

theorem tie_next {B : BlakeRel} {mem : Nat → E} {xs : Nat → Nat} {s : Nat} {z : Bool}
    (hp : FreeLastVM.PathFacts B mem xs s z) {u : Nat} (hu : u+1 < 13) :
    mem (accCell (u+1)) = mem (accCell u) + cellOfBits (part (u+1) (xs (u+1))) := by
  have hmem : ∀ ci ∈ FreeLastBlocks.tie (u+1) (xs (u+1)), ci.RelB B mem :=
    fun ci hci => hp.tie_rel hu hci
  unfold FreeLastBlocks.tie at hmem
  rw [if_neg (by omega : u+1 ≠ 0),Nat.add_sub_cancel] at hmem
  cases hh : FreeLastBlocks.hinted (u+1) (xs (u+1)) with
  | true =>
    simp only [hh,if_true] at hmem
    have h : mem (accCell (u+1)) = mem (accCell u)+mem (hCell (u+1+1)) := hmem _ (List.mem_singleton_self _)
    rw [h,landing_part (hp.landing (u+1) hu) hh]
  | false =>
    simp only [hh,Bool.false_eq_true,if_false] at hmem
    rw [part_plain hu (hp.valid _ hu) hh]
    by_cases hv : xs (u+1) = 0
    · rw [if_pos hv] at hmem
      have h : mem (accCell (u+1)) = mem (accCell u)*mem oneCell := hmem _ (List.mem_singleton_self _)
      rw [h,FreeLastVM.pro_one hp.pro,oneV,FreeLastVM.checksum_embed_one,mul_one,hv,pattern_zero,add_zero]
    · rw [if_neg hv] at hmem
      have hs : mem (tCell (u+1)) = FreeLastBlocks.pattern (u+1) (xs (u+1)) := hmem _ List.mem_cons_self
      have he : mem (accCell (u+1)) = mem (accCell u)+mem (tCell (u+1)) :=
        hmem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      rw [he,hs]

theorem acc_path {B : BlakeRel} {mem : Nat → E} {xs : Nat → Nat} {s : Nat} {z : Bool}
    (hp : FreeLastVM.PathFacts B mem xs s z) :
    ∀ u < 13, mem (accCell u) = cellOfBits (accBits (fun w => if w < 13 then xs w else 0) u) := by
  let x := fun w => if w < 13 then xs w else 0
  have hx : ∀ w, x w < 2^gb w := by
    intro w
    by_cases hw : w < 13
    · simp only [x,if_pos hw]; exact lt_of_lt_of_le (hp.valid w hw) (VF_le w hw)
    · simp only [x,if_neg hw]; positivity
  intro u hu
  change mem (accCell u) = cellOfBits (accBits x u)
  induction u with
  | zero =>
    rw [acc_zero x hx]
    simpa only [x,if_pos (by decide : 0 < 13)] using tie_first hp
  | succ u ih =>
    rw [tie_next hp hu,ih (by omega),show xs (u+1) = x (u+1) from (if_pos hu).symm,
      cellOfBits_add,acc_step x hx hu]

theorem fields_of_path {B : BlakeRel} {mem : Nat → E} {xs : Nat → Nat} {s : Nat} {z : Bool}
    (hp : FreeLastVM.PathFacts B mem xs s z) {u : Nat} (hu : u < 13) :
    field u (remask (decodeRaw (cellBits (mem idxCell)))) = xs u := by
  let x := fun w => if w < 13 then xs w else 0
  have hx : ∀ w, x w < 2^gb w := by
    intro w
    by_cases hw : w < 13
    · simp only [x,if_pos hw]; exact lt_of_lt_of_le (hp.valid w hw) (VF_le w hw)
    · simp only [x,if_neg hw]; positivity
  have ha := acc_path hp 12 (by decide)
  change mem idxCell = cellOfBits (accBits x 12) at ha
  rw [ha,LeanIsa.cellBits_cellOfBits,acc_encode x hx,decode_encode_raw,field,unmask_remask,
    pack_digit x hx hu]
  exact if_pos hu

theorem acc_digits (I : BitVec 128) :
    accBits (fun w => digitW gb (decodeRaw I).toNat w) 12 = I := by
  rw [acc_encode _ (fun w => digitW_lt _ _ _)]
  have hp : pack (fun w => digitW gb (decodeRaw I).toNat w) = decodeRaw I := by
    unfold pack
    rw [ofDigitsW_digitW gb _ 13 (by change (decodeRaw I).toNat < 2^128; exact (decodeRaw I).isLt),
      BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rw [hp,encode_decode_raw]

end
end OptimalOTS.FreeLastTie
