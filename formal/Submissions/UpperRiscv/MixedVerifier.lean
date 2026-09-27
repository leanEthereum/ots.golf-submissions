import Submissions.UpperRiscv.MixedPhase
import Submissions.UpperRiscv.MixedStagedCost

namespace OptimalOTS.RiscvMixedProgram

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open scoped Classical
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] stagedBlocks stagedCost

theorem index_take (bits : List Bool) : ofBits 128 (bits.take 128) = ofBits 128 bits := by
  simpa only [List.drop_zero] using
    ofBits_drop_take bits (cap := 128) (start := 0) (len := 128) le_rfl

theorem image_code : image.code = verifier := rfl

/-- The certified cycle bound on every execution. -/
def cycleBound : ℕ := 345

/-- A slice inside the first 5504 bits reads the same from the loaded, zero-extended signature. -/
theorem padded_drop (bits : List Bool) (off n : ℕ) (h : off + n ≤ 5504) :
    ofBits n ((padded bits).drop off) = ofBits n (bits.drop off) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofBits, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, testBit_foldr_bits,
    List.getD_eq_getElem?_getD, List.getElem?_drop, padded, List.getElem?_append,
    List.length_take, List.getElem?_take, List.getElem?_replicate]
  split_ifs <;> first | rfl | omega | (rw [List.getElem?_eq_none (by omega)]; rfl) | simp_all

theorem countByte_eq (bits : List Bool) : countByte bits = rawCountByte bits := by
  unfold countByte rawCountByte
  rw [padded_drop bits 5456 8 (by norm_num)]

theorem initial_chains (pk : PublicKey) (m : Message) (bits : List Bool) (answer : BitVec hashBits)
    (located : Riscv.CodeAt (S0 pk m bits) (W 4096) verifier) :
    ChainsInv (rawIdx answer) (rawCountByte bits) ((padded bits).drop 128) pk
      (min bits.length 5505) (afterIndex pk m bits answer) (fun _ => 0) 0 := by
  refine ⟨afterIndex_ctx pk m bits answer located,
    (afterIndex_setupRegs pk m bits answer).2, ?_, (afterIndex_setupRegs pk m bits answer).1,
    ?_, ?_, ?_⟩
  · intro h; omega
  · intro j hj
    rw [List.drop_drop, padded_drop bits _ _ (by have := wireOffset_contained j; omega),
      ← List.drop_drop]
    exact afterIndex_payloadFrom pk m bits answer j hj
  · intro j hj; omega
  · exact afterIndex_tail pk m bits answer

theorem stagedVerify_unfold (pk : PublicKey) (m : Message) (bits : List Bool) :
    some <$> stagedVerify pk m bits = (do
      let answer ← hash (swapHalves (emsg m pk ++ ofBits nonceBits bits))
      if CountCheck (pack answer) (rawCountByte bits) then
        (runNodes' (rawIdx answer) (rawCountByte bits) (Payload.permute ((padded bits).drop 128))
          (entryNodes (rawIdx answer) (rawCountByte bits) 0) (fun _ => 0) (Payload.graphOff 0) >>=
          fun r => if rawCountByte bits < 16 then
            runNodes' (rawIdx answer) (rawCountByte bits) (Payload.permute ((padded bits).drop 128))
              (tableNodes (rawIdx answer) (rawCountByte bits) 0) r.1 r.2 >>= fun r' =>
              some <$> stagedBlocks (rawIdx answer) (rawCountByte bits)
                (Payload.permute ((padded bits).drop 128)) pk (min bits.length 5505)
                (ofBits 48 (((padded bits).drop 128).drop 5328)) 16 0 r'.1 r'.2
            else pure (some false))
      else pure (some false)) := by
  rw [stagedVerify_eq]
  have ht : ofBits nonceBits (bits.take 128) = ofBits nonceBits bits := index_take bits
  rw [ht, map_bind, ← countByte_eq]
  apply bind_congr_of_forall_mem_support
  intro answer _
  have htail : sigTail bits = ofBits 48 (((padded bits).drop 128).drop 5328) := by
    unfold sigTail; rw [List.drop_drop]
  by_cases hc : CountCheck (pack answer) (countByte bits)
  · have hc' : (digitSum (pack answer) + countByte bits) % 255 = 146 := hc
    rw [if_pos hc', if_pos hc]
    unfold stagedChains
    rw [htail, map_bind]
    refine bind_congr (fun r => ?_)
    split_ifs <;> simp only [map_bind, map_pure]
    rfl
  · have hc' : ¬ (digitSum (pack answer) + countByte bits) % 255 = 146 := hc
    rw [if_neg hc', if_neg hc, map_pure]

/-- Every accepted and rejected execution follows the staged verifier's exact oracle trace. -/
theorem image_refines (pk : PublicKey) (m : Message) (bits : List Bool) :
    Riscv.Refines 1337 (Riscv.initialState image pk m bits) (some <$> stagedVerify pk m bits)
      cycleBound := by
  have located := Riscv.CodeAt.initial image pk m bits image_valid
  rw [image_code] at located
  have pc0 : (Riscv.initialState image pk m bits).pc = Riscv.codeBase := by
    simp [Riscv.initialState]
  rw [← pc0] at located
  have global : Riscv.CodeAt (Riscv.initialState image pk m bits) (W 4096) verifier := by
    rw [pc0] at located
    exact located
  have e : verifier = indexPhase ++ (freePrologue ++ freeTable ++ prologue 0 ++ tables) := by
    simp only [verifier, List.append_assoc]
  rw [e] at located
  rw [stagedVerify_unfold, show cycleBound = 310 + 35 from rfl]
  have hwire : 5328 ≤ ((padded bits).drop 128).length := by
    rw [List.length_drop, length_padded]; norm_num
  apply indexPhase_refines pk m bits _ 1299 1337 _ 310 (by norm_num) located
    (by rw [indexPhase_length])
  intro answer check left hleft
  set v := rawCountByte bits
  have hv256 : v < 256 := countByte_lt bits
  have inv := initial_chains pk m bits answer global
  have pc := afterIndex_pc pk m bits answer
  have small : v < 16 → 6 + v + stagedCost (rawIdx answer) v 16 0 ≤ 310 :=
    fun hs => stagedCost_le (rawIdx answer) v hs check
  have run := free_refines (rawIdx answer) v ((padded bits).drop 128) pk hv256
    (fun r' => some <$> stagedBlocks (rawIdx answer) v (Payload.permute ((padded bits).drop 128)) pk
      (min bits.length 5505) (ofBits 48 (((padded bits).drop 128).drop 5328)) 16 0 r'.1 r'.2)
    (stagedCost (rawIdx answer) v 16 0) (if v < 16 then stagedCost (rawIdx answer) v 16 0 else 0)
    hwire ?_ (afterIndex pk m bits answer) (fun _ => 0) left inv (by rw [pc]; rfl)
    (by split_ifs with hs <;> [have := small hs; skip] <;> omega)
  · refine run.mono ?_
    unfold freeCost
    split_ifs with hs
    · have := small hs
      omega
    · omega
  · intro u z hs invU locU left' hleft'
    rw [if_pos hs] at hleft'
    have h := stagedBlocks_refines (rawIdx answer) v ((padded bits).drop 128) pk hs hwire 16 0 rfl
      (by norm_num) u z left' invU ⟨[], by simpa [blockCodeAt] using locU⟩ hleft'
    simpa using h

end OptimalOTS.RiscvMixedProgram
