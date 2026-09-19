import Submissions.UpperRiscv.ChainBlock

/-!
# The chain phase

The 32 chain blocks run one after the other, in the specification's chain-major node order.
After chain `k`, the tops of chains `0 … k` with the headers between them form the prefix of the
root input in memory. The phase costs `9 + 2 · nibble` cycles per chain, `608` in all.
-/

namespace OptimalOTS.RiscvUpperProgram

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx) (payload : List Bool) (pk : PublicKey)

/-- The word read for a 128-bit node is the specification's decoded value. -/
theorem read_value (k : ℕ) (n : Name) (hn : graph.len n.fin = 128) (cursor : ℕ)
    (t : MachineState) (held : Holds t k (ofBits 128 (payload.drop cursor))) :
    Holds t k (ofBits (graph.len n.fin) ((payload.drop cursor).take (graph.len n.fin))) := by
  unfold Holds
  rw [hn]
  have take : ofBits 128 ((payload.drop cursor).take 128) = ofBits 128 (payload.drop cursor) := by
    simpa only [List.drop_zero] using
      ofBits_drop_take (payload.drop cursor) (cap := 128) (start := 0) (len := 128) (by decide)
  rw [take]
  exact held

/-- The root prefix grows by the header and the top of chain `k`. -/
theorem rootAcc_extend (s : MachineState) (k : ℕ) (hk : k < 32) (c : ℕ → BitVec 128)
    (prev : 1 ≤ k → MemBits s (W Flat.slotBase) (rootAcc c (k - 1)))
    (header : s.getMem (W (Flat.slotAddr k - 8)) = rootHdr k)
    (value : MemBits s (slotW k) (c k)) : MemBits s (W Flat.slotBase) (rootAcc c k) := by
  have hs := slot_bounds k hk
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    exact value
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj := prev (by omega)
    rw [show j + 1 - 1 = j by omega] at hj
    rw [rootAcc]
    apply (memBits_cast _ _ _ _).mpr
    apply memBits_append (by omega) hj
    have base : W Flat.slotBase + BitVec.ofNat 64 ((128 + 192 * j) / 8) =
        W (Flat.slotAddr (j + 1) - 8) := by
      rw [W_add]
      congr 1
      unfold Flat.slotAddr
      omega
    rw [base]
    apply memBits_append (by decide)
    · have h := memBits_word s (W (Flat.slotAddr (j + 1) - 8)) (aligned_W _ (by omega) (by omega))
      rw [header] at h
      exact h
    · rw [show (64 : ℕ) / 8 = 8 by norm_num, W_add,
        show Flat.slotAddr (j + 1) - 8 + 8 = Flat.slotAddr (j + 1) by omega]
      exact value

/-- One chain: its prologue, then the levels from its disclosed position, at
`9 + 2 (15 - p)` cycles. -/
theorem chain_refines (k : Fin 32) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      ChainsInv index payload pk u y (k.val + 1) → Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, 128 * k.val + 128)) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : ChainsInv index payload pk s x k.val)
    (located : Riscv.CodeAt s s.pc (chainBlock k ++ tail))
    (bound : 9 + 2 * (15 - pos index k) + rest' ≤ fuel) :
    Riscv.Refines fuel s (runNodes' index payload (chainNodes k) x (128 * k.val) >>= K)
      (9 + 2 * (15 - pos index k) + c) := by
  have hp := pos_le index k
  have hs := slot_bounds k k.isLt
  -- the specification up to the disclosed level is pure
  obtain ⟨x', run, frame, value⟩ := prefix_run index payload k (pos index k) le_rfl x (128 * k.val)
  rw [if_pos rfl] at run
  have nodes : chainNodes k = (src k :: (List.range (pos index k)).flatMap (tripleN k)) ++
      (List.range' (pos index k) (15 - pos index k)).flatMap (tripleN k) := by
    rw [chainNodes_eq, range_split (pos index k) hp, List.flatMap_append, List.cons_append]
  rw [nodes, runNodes'_append, run, bind_assoc, pure_bind]
  dsimp only
  -- the prologue
  rw [chainBlock, List.append_assoc] at located
  rw [show fuel = 9 + (fuel - 9) by omega,
    show 9 + 2 * (15 - pos index k) + c = 9 + (2 * (15 - pos index k) + c) by omega]
  apply prologue_refines index payload pk k (chainTable ++ tail) s x inv located
  intro u inv' held code
  have locatedU : Riscv.CodeAt u u.pc
      ((List.range' (pos index k) (15 - pos index k)).flatMap chainStep ++ tail) := by
    have h := CodeAt.drop located (9 + 2 * pos index k)
    have split : chainPrologue k ++ (chainTable ++ tail) =
        (chainPrologue k ++ (List.range (pos index k)).flatMap chainStep) ++
        ((List.range' (pos index k) (15 - pos index k)).flatMap chainStep ++ tail) := by
      rw [chainTable_split (pos index k) hp]
      simp only [List.append_assoc]
    have hlen : (chainPrologue k ++ (List.range (pos index k)).flatMap chainStep).length =
        9 + 2 * pos index k := by
      rw [List.length_append, chainPrologue_parts, List.length_append, prologueLinear_length,
        steps_length, List.length_range]
      rfl
    rw [split, List.drop_left' hlen, inv.pc, W_add, ← show blockStart k + 4 * (9 + 2 * pos index k) =
      blockStart k + 4 * (9 + 2 * pos index k) from rfl, ← inv'.pc] at h
    exact h.code_eq code
  have inv'' : StepInv index payload pk u x' k (pos index k) := by
    refine ⟨inv'.ctx, inv'.slot, inv'.input, inv'.header, inv'.pc, ?_⟩
    intro hk1
    have e : rootAcc (topFun (tops x')) (k.val - 1) = rootAcc (topFun (tops x)) (k.val - 1) := by
      apply rootAcc_congr
      intro i hi
      unfold topFun tops
      split_ifs with hi32
      · rw [frame ⟨i, hi32⟩ (by intro e; have := congrArg Fin.val e; simp at this; omega)]
      · rfl
    rw [e]
    exact inv'.done hk1
  have held' : Holds u k (x' (valueNode k (pos index k)).fin) := by
    rw [value rfl]
    exact read_value payload k _ (valueNode_len k _ hp) _ u held
  apply steps_refines index payload pk k tail K c rest' (128 * k.val + 128) ?_
    (15 - pos index k) (pos index k) rfl hp le_rfl u x' (fuel - 9) inv'' held' locatedU (by omega)
  intro v y invV heldV locatedV left hleft
  apply continuation v y ?_ locatedV left hleft
  obtain ⟨L, hL, hhdr, h15⟩ := invV.header
  have L0 : L = 0 := h15 rfl
  subst L0
  refine ⟨invV.ctx, ?_, ?_, ?_⟩
  · rw [invV.slot]
    unfold prevSlot
    rw [if_neg (by omega)]
    rfl
  · rw [invV.pc]
    congr 1
  · intro _
    rw [show k.val + 1 - 1 = k.val by omega]
    apply rootAcc_extend v k k.isLt _ invV.done
    · rw [hhdr]
      simp [hdrW, rootHdr]
    · have h := heldV.trunc
      unfold topFun tops
      rw [dif_pos k.isLt]
      exact h

/-! ## All chains -/

/-- Chains `k` and later, in specification order. -/
def chainsFrom (k : ℕ) : List Name :=
  if h : k < 32 then chainNodes ⟨k, h⟩ ++ chainsFrom (k + 1) else []
termination_by 32 - k

/-- The blocks of chains `k` and later. -/
def blocksFrom (k : ℕ) : Code :=
  if k < 32 then chainBlock k ++ blocksFrom (k + 1) else []
termination_by 32 - k

set_option maxRecDepth 100000 in
theorem chainsFrom_zero : (List.finRange 32).flatMap chainNodes = chainsFrom 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem blocks_eq : chains = blocksFrom 0 := by
  decide +kernel

theorem blocksFrom_nil (k : ℕ) (hk : ¬ k < 32) : blocksFrom k = [] := by
  rw [blocksFrom, if_neg hk]

theorem blocksFrom_cons (k : ℕ) (hk : k < 32) :
    blocksFrom k = chainBlock k ++ blocksFrom (k + 1) := by
  rw [blocksFrom, if_pos hk]

/-- The cycles of chains `k` and later. -/
def costFrom (k : ℕ) : ℕ :=
  if h : k < 32 then 9 + 2 * (15 - pos index ⟨k, h⟩) + costFrom (k + 1) else 0
termination_by 32 - k

theorem costFrom_eq : ∀ (n k : ℕ), 32 - k = n → costFrom index k =
    ∑ k' : Fin 32, if k ≤ k'.val then 9 + 2 * (15 - pos index k') else 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    rw [costFrom, dif_neg (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro k' _
    rw [if_neg]
    have := k'.isLt
    omega
  | succ n ih =>
    intro k hk
    have hk32 : k < 32 := by omega
    rw [costFrom, dif_pos hk32, ih (k + 1) (by omega)]
    have single : 9 + 2 * (15 - pos index ⟨k, hk32⟩) =
        ∑ k' : Fin 32, if k' = ⟨k, hk32⟩ then
          (if k ≤ k'.val then 9 + 2 * (15 - pos index k') else 0) else 0 := by
      rw [Finset.sum_ite_eq' Finset.univ (⟨k, hk32⟩ : Fin 32)
        (fun k' : Fin 32 => if k ≤ k'.val then 9 + 2 * (15 - pos index k') else 0),
        if_pos (Finset.mem_univ _)]
      simp only [le_refl, if_true]
    rw [single, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k' _
    by_cases he : k' = ⟨k, hk32⟩
    · subst he
      simp only [↓reduceIte, le_refl]
      split_ifs <;> omega
    · rw [if_neg he, Nat.zero_add]
      have hne : k'.val ≠ k := fun h => he (Fin.ext h)
      split_ifs <;> omega

/-- The 32 prologues and 160 hash steps cost 608 cycles on every accepted index. -/
theorem costFrom_zero : costFrom index 0 = 608 := by
  rw [costFrom_eq index 32 0 rfl]
  simp only [Nat.zero_le, if_true]
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, smul_eq_mul]
  have hs : ∑ k' : Fin 32, (15 - pos index k') = target := by
    have := fixedPositions_sum index
    simpa only [pos] using this
  rw [hs]
  rfl

/-- Chains `k` and later refine the reader over their nodes. -/
theorem chainsFrom_refines (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      ChainsInv index payload pk u y 32 → Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, 4096)) c) :
    ∀ (n k : ℕ), 32 - k = n → k ≤ 32 →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel : ℕ),
      ChainsInv index payload pk s x k →
      Riscv.CodeAt s s.pc (blocksFrom k ++ tail) →
      (blocksFrom k).length + rest' ≤ fuel →
      Riscv.Refines fuel s (runNodes' index payload (chainsFrom k) x (128 * k) >>= K)
        (costFrom index k + c) := by
  intro n
  induction n with
  | zero =>
    intro k hk hk' s x fuel inv located bound
    have hk32 : k = 32 := by omega
    subst hk32
    rw [chainsFrom, dif_neg (by omega), costFrom, dif_neg (by omega), Nat.zero_add, runNodes',
      pure_bind]
    rw [blocksFrom_nil 32 (by omega), List.nil_append] at located
    rw [blocksFrom_nil 32 (by omega), List.length_nil, Nat.zero_add] at bound
    exact continuation s x inv located fuel bound
  | succ n ih =>
    intro k hk hk' s x fuel inv located bound
    have hk32 : k < 32 := by omega
    rw [chainsFrom, dif_pos hk32, costFrom, dif_pos hk32, runNodes'_append, bind_assoc]
    rw [blocksFrom_cons k hk32, List.append_assoc] at located
    rw [blocksFrom_cons k hk32, List.length_append, chainBlock_length] at bound
    have hp := pos_le index ⟨k, hk32⟩
    rw [Nat.add_assoc]
    apply chain_refines index payload pk ⟨k, hk32⟩ (blocksFrom (k + 1) ++ tail)
      (fun r => runNodes' index payload (chainsFrom (k + 1)) r.1 r.2 >>= K)
      (costFrom index (k + 1) + c) ((blocksFrom (k + 1)).length + rest') ?_ s x fuel inv located
      (by omega)
    intro u y inv' located' left hleft
    dsimp only
    rw [show 128 * k + 128 = 128 * (k + 1) by ring]
    exact ih (k + 1) (by omega) (by omega) u y left inv' located' hleft

end OptimalOTS.RiscvUpperProgram
