import Submissions.UpperLeanIsa.PartialHintCodec

/-! The three-hint codec has the same 127-bit effective index and exactly
2^129 raw oracle outputs over each index. -/
namespace OptimalOTS.LeanIsaBaseline.Layer

def indexSlice {n : Nat} (w : BitVec n) : Index :=
  PartialHints.effectiveIndex (w.extractLsb' 0 128)
def indexRest (w : BitVec 256) : BitVec 129 := PartialHints.rest w
def joinIndex (i : Index) (r : BitVec 129) : BitVec 256 := PartialHints.join i r

theorem indexSlice_effective (w : BitVec 256) :
    indexSlice w = PartialHints.effectiveIndex (w.extractLsb' 0 128) := rfl

theorem joinIndex_split (w : BitVec 256) : joinIndex (indexSlice w) (indexRest w) = w :=
  PartialHints.join_split w
theorem indexSlice_join (i : Index) (r : BitVec 129) : indexSlice (joinIndex i r) = i :=
  PartialHints.slice_join i r
theorem indexRest_join (i : Index) (r : BitVec 129) : indexRest (joinIndex i r) = r :=
  PartialHints.rest_join i r
theorem card_indexSlice (p : Index → Prop) [DecidablePred p] :
    (Finset.univ.filter fun w : BitVec 256 => p (indexSlice w)).card =
      (Finset.univ.filter p).card * 2^129 := PartialHints.card_slice p

end OptimalOTS.LeanIsaBaseline.Layer
