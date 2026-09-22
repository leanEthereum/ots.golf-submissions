import Submissions.UpperRiscv.ChainSteps

/-!
# One block: a pair of chains, or a single chain

A block's prologue lands on the hash step of the first chain's disclosed position; the steps from
there to the end of its table hash the chain up to its top. In a pair block the switch then moves
the pointers to the second chain, whose table in the selected copy has exactly the steps from
its disclosed position. The specification's nodes below a disclosed position are pure zeros.
-/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx) (payload : List Bool) (pk : PublicKey)

/-! ## Code shapes -/

/-- The three nodes of level `t` of chain `k`. -/
def tripleN (k : Fin 28) (t : ℕ) : List Name :=
  if h : t < 32 then [ci k ⟨t, h⟩, ch k ⟨t, h⟩, cv k ⟨t, h⟩] else []

theorem chainNodes_eq (k : Fin 28) :
    chainNodes k = src k :: (List.range 32).flatMap (tripleN k) := by
  simp only [chainNodes, List.finRange, List.range]
  rfl

theorem range_split (p : ℕ) (hp : p ≤ 32) :
    List.range 32 = List.range p ++ List.range' p (32 - p) := by
  have h := @List.range'_append_1 0 p (32 - p)
  rw [Nat.zero_add, Nat.add_sub_cancel' hp] at h
  rw [List.range_eq_range', List.range_eq_range', h]

/-! ## Locating code -/

/-- Landing inside a located block. -/
theorem CodeAt.drop {s : MachineState} {pc : Word} {code : List Instr}
    (located : Riscv.CodeAt s pc code) (i : ℕ) :
    Riscv.CodeAt s (pc + BitVec.ofNat 64 (4 * i)) (code.drop i) := by
  intro n hn
  have h := located (i + n) (by rw [List.length_drop] at hn; omega)
  rw [List.getElem?_drop, ← h, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

/-- A prefix of a suffix of located code is located. -/
theorem CodeAt.of_drop {s : MachineState} {pc : Word} {code l1 l2 : List Instr}
    (located : Riscv.CodeAt s pc code) (n : ℕ) (h : code.drop n = l1 ++ l2) :
    Riscv.CodeAt s (pc + BitVec.ofNat 64 (4 * n)) l1 := by
  have := CodeAt.drop located n
  rw [h] at this
  exact this.append_left

/-- Dropping whole blocks of a fixed length from a flat map. -/
theorem drop_flatMap_fixed {α : Type} (f : ℕ → List α) (L : ℕ) :
    ∀ (i a n : ℕ), i < n → (∀ m, m < n → (f (a + m)).length = L) →
    ((List.range' a n).flatMap f).drop (L * i) =
      f (a + i) ++ (List.range' (a + i + 1) (n - (i + 1))).flatMap f := by
  intro i
  induction i with
  | zero =>
    intro a n hi hL
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [List.range'_succ, List.flatMap_cons]
  | succ i ih =>
    intro a n hi hL
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have h0 : (f (a + 0)).length = L := hL 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [List.range'_succ, List.flatMap_cons, show L * (i + 1) = L + L * i by ring,
      ← List.drop_drop, List.drop_left' h0]
    rw [ih (a + 1) n' (by omega) (fun m hm => by
      rw [show a + 1 + m = a + (m + 1) by omega]; exact hL (m + 1) (by omega))]
    have e1 : a + 1 + i = a + (i + 1) := by omega
    have e2 : n' - (i + 1) = n' + 1 - (i + 1 + 1) := by omega
    rw [e1, e2]

theorem copyCode_length (q dB : ℕ) (hdB : dB < 16) : (copyCode q dB).length = 64 := by
  simp [copyCode, switch, prologue]
  omega

theorem innerCode_length (g c : ℕ) (hc : c < 16) :
    ((List.range 4).flatMap fun j => copyCode (4 * g + j) (15 - c)).length = 256 := by
  simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_singleton,
    List.nil_append, List.length_append]
  rw [copyCode_length _ _ (by omega), copyCode_length _ _ (by omega),
    copyCode_length _ _ (by omega), copyCode_length _ _ (by omega)]

theorem groupCode_length (g : ℕ) : (groupCode g).length = 4096 := by
  unfold groupCode
  rw [List.length_flatMap, List.map_congr_left (fun c hc => innerCode_length g c
    (List.mem_range.mp hc))]
  simp

theorem pairsCode_length : pairsCode.length = 12288 := by
  unfold pairsCode
  rw [List.length_flatMap]
  simp [groupCode_length]

theorem indexPhase_length' : (indexPhase ++ prologue 0).length = 52 := by decide

theorem verifier_drop_52 : verifier.drop 52 = pairsCode ++ (singlesCode ++ (root ++ decision)) := by
  have : verifier = (indexPhase ++ prologue 0) ++ (pairsCode ++ (singlesCode ++ (root ++ decision))) := by
    simp [verifier]
  rw [this, List.drop_left' indexPhase_length']

/-- The code address of copy `dB` of pair `q`, as an offset into the image. -/
theorem copyStart_eq (q dB : ℕ) :
    copyStart q dB = 4096 + 4 * (52 + (4096 * (q / 4) + (256 * (15 - dB) + 64 * (q % 4)))) := by
  unfold copyStart copiesStart indexLength; omega

theorem pairsCode_drop (g r : ℕ) (hg : g < 3) (hr : r < 4096) :
    pairsCode.drop (4096 * g + r) = (groupCode g).drop r ++
      (List.range' (g + 1) (3 - (g + 1))).flatMap groupCode := by
  unfold pairsCode
  rw [List.range_eq_range', ← List.drop_drop, drop_flatMap_fixed groupCode 4096 g 0 3 hg
    (fun m _ => by rw [Nat.zero_add]; exact groupCode_length m), Nat.zero_add,
    List.drop_append_of_le_length (by rw [groupCode_length]; omega)]

theorem groupCode_drop (g c r : ℕ) (hc : c < 16) (hr : r < 256) :
    (groupCode g).drop (256 * c + r) =
      ((List.range 4).flatMap fun j => copyCode (4 * g + j) (15 - c)).drop r ++
        (List.range' (c + 1) (16 - (c + 1))).flatMap
          fun c => (List.range 4).flatMap fun j => copyCode (4 * g + j) (15 - c) := by
  unfold groupCode
  rw [List.range_eq_range' (n := 16), ← List.drop_drop,
    drop_flatMap_fixed (fun c => (List.range 4).flatMap fun j => copyCode (4 * g + j) (15 - c))
      256 c 0 16 hc (fun m hm => by rw [Nat.zero_add]; exact innerCode_length g m hm), Nat.zero_add,
    List.drop_append_of_le_length (by rw [innerCode_length g c hc]; omega)]

theorem innerCode_drop (g c j : ℕ) (hc : c < 16) (hj : j < 4) :
    ((List.range 4).flatMap fun j => copyCode (4 * g + j) (15 - c)).drop (64 * j) =
      copyCode (4 * g + j) (15 - c) ++
        (List.range' (j + 1) (4 - (j + 1))).flatMap fun j => copyCode (4 * g + j) (15 - c) := by
  rw [List.range_eq_range' (n := 4), drop_flatMap_fixed _ 64 j 0 4 hj
    (fun m _ => by rw [Nat.zero_add]; exact copyCode_length _ _ (by omega)), Nat.zero_add]

/-- Copy `dB` of pair `q` is located at `copyStart q dB`. -/
theorem copy_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier) (q dB : ℕ)
    (hq : q < 12) (hdB : dB < 16) :
    ∃ rest, Riscv.CodeAt s (W (copyStart q dB)) (copyCode q dB ++ rest) := by
  set g := q / 4 with hg
  set j := q % 4 with hj
  set c := 15 - dB with hc
  have hg3 : g < 3 := by omega
  have hj4 : j < 4 := by omega
  have hc16 : c < 16 := by omega
  have hqe : 4 * g + j = q := by omega
  have hdBe : 15 - c = dB := by omega
  have e : verifier.drop (52 + (4096 * g + (256 * c + 64 * j))) =
      copyCode q dB ++ (((List.range' (j + 1) (4 - (j + 1))).flatMap
          fun j => copyCode (4 * g + j) (15 - c)) ++
        ((List.range' (c + 1) (16 - (c + 1))).flatMap
          fun c => (List.range 4).flatMap fun j => copyCode (4 * g + j) (15 - c)) ++
        ((List.range' (g + 1) (3 - (g + 1))).flatMap groupCode ++
          (singlesCode ++ (root ++ decision)))) := by
    rw [← List.drop_drop, verifier_drop_52, List.drop_append_of_le_length (by
      rw [pairsCode_length]; omega),
      pairsCode_drop g _ hg3 (by omega), groupCode_drop g c _ hc16 (by omega),
      innerCode_drop g c j hc16 hj4, hqe, hdBe]
    simp only [List.append_assoc]
  have h := CodeAt.drop global (52 + (4096 * g + (256 * c + 64 * j)))
  rw [e] at h
  rw [copyStart_eq q dB, ← W_add]
  exact ⟨_, h⟩

/-- The tail of single block `s'`: the next prologue, or the root and the decision. -/
def singleTail (s' : ℕ) : Code := if s' < 3 then prologue (13 + s') else root ++ decision

theorem singlesStart_eq : singlesStart = 4096 + 4 * (52 + 12288) := by
  unfold singlesStart copiesStart indexLength; omega

/-- The table of single block `12 + s'` is located at `singleTableStart s'`, followed by its
tail. -/
theorem single_located (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier) (s' : ℕ)
    (hs : s' < 4) :
    ∃ rest, Riscv.CodeAt s (W (singleTableStart s'))
      (List.replicate 32 .ECALL ++ (singleTail s' ++ rest)) := by
  have e0 : verifier.drop (52 + 12288) = singlesCode ++ (root ++ decision) := by
    rw [← List.drop_drop, verifier_drop_52, List.drop_append_of_le_length (by
      rw [pairsCode_length]), List.drop_eq_nil_of_le (by rw [pairsCode_length]), List.nil_append]
  have hs' : singleTableStart s' = 4096 + 4 * (52 + 12288 + 36 * s') := by
    unfold singleTableStart; rw [singlesStart_eq]; ring
  have key : (singlesCode ++ (root ++ decision)).drop (36 * s') =
      List.replicate 32 .ECALL ++ (singleTail s' ++
        (singlesCode ++ (root ++ decision)).drop (36 * s' + 32 + (singleTail s').length)) := by
    interval_cases s' <;> decide +kernel
  have e : verifier.drop (52 + 12288 + 36 * s') =
      List.replicate 32 .ECALL ++ (singleTail s' ++
        (singlesCode ++ (root ++ decision)).drop (36 * s' + 32 + (singleTail s').length)) := by
    rw [← List.drop_drop, e0, key]
  have h := CodeAt.drop global (52 + 12288 + 36 * s')
  rw [e] at h
  rw [hs', ← W_add]
  exact ⟨_, h⟩

/-- Landing at position `p` of a 32-step table. -/
theorem landing_code {s : MachineState} {base : ℕ} {tail : Code}
    (located : Riscv.CodeAt s (W base) (List.replicate 32 .ECALL ++ tail)) (p : ℕ) (hp : p ≤ 32) :
    Riscv.CodeAt s (W (base + 4 * p)) (List.replicate (32 - p) .ECALL ++ tail) := by
  have h := CodeAt.drop located p
  rw [List.drop_append_of_le_length (by simp; omega), List.drop_replicate] at h
  rw [← W_add]
  exact h

/-! ## The specification before the disclosed level -/

/-- Before its disclosed level, a chain's nodes are pure zeros. -/
theorem prefix_run (k : Fin 28) :
    ∀ (q : ℕ), q ≤ RiscvUpperForest.ForestVerifier.pos index k → ∀ (x : graph.Assignment) (cursor : ℕ),
    ∃ x' : graph.Assignment,
      runNodes' index payload (src k :: (List.range q).flatMap (tripleN k)) x cursor =
        pure (x', cursor) ∧
      (∀ k' : Fin 28, k' ≠ k → x' (cv k' 31).fin = x (cv k' 31).fin) := by
  intro q
  induction q with
  | zero =>
    intro _ x cursor
    have run : runNodes' index payload (src k :: (List.range 0).flatMap (tripleN k)) x cursor =
        cursorStep index payload x cursor (src k) := by
      simp only [List.range_zero, List.flatMap_nil, runNodes', Prod.mk.eta, bind_pure]
    rw [run, cursorStep_src]
    refine ⟨_, rfl, ?_⟩
    intro k' _
    exact Function.update_of_ne (fin_ne_of_ne (by simp)) _ _
  | succ q ih =>
    intro hq x cursor
    obtain ⟨x₁, run₁, frame₁⟩ := ih (by omega) x cursor
    have hq32 : q < 32 := by
      have := pos_le index k
      omega
    have hne : ¬ (RiscvUpperForest.ForestVerifier.pos index k = q) := by omega
    have hlt : ¬ (RiscvUpperForest.ForestVerifier.pos index k < q) := by omega
    have hle : ¬ (RiscvUpperForest.ForestVerifier.pos index k ≤ q) := by omega
    have triple : tripleN k q = [ci k ⟨q, hq32⟩, ch k ⟨q, hq32⟩, cv k ⟨q, hq32⟩] := by
      simp [tripleN, hq32]
    have run : runNodes' index payload (src k :: (List.range (q + 1)).flatMap (tripleN k)) x cursor =
        runNodes' index payload [ci k ⟨q, hq32⟩, ch k ⟨q, hq32⟩, cv k ⟨q, hq32⟩] x₁ cursor := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, triple, ← List.cons_append,
        runNodes'_append, run₁, pure_bind]
    rw [run]
    simp only [runNodes', cursorStep_ci, cursorStep_ch, cursorStep_cv, if_neg hne, if_neg hlt,
      if_neg hle, pure_bind, Prod.mk.eta, bind_pure]
    refine ⟨_, rfl, ?_⟩
    intro k' hk'
    rw [Function.update_of_ne (fin_ne_of_ne (fun h => hk' (Name.cv.inj h).1)),
      Function.update_of_ne (fin_ne_of_ne (by simp)),
      Function.update_of_ne (fin_ne_of_ne (by simp))]
    exact frame₁ k' hk'

/-! ## The invariant between chains -/

/-- Machine facts holding between chains: chains before `k` are complete, the low 192 bits of
their tops form the prefix of the root input, and the full top of chain `k - 1` still lies below
its slot. -/
structure ChainsInv (s : MachineState) (x : graph.Assignment) (k : ℕ) : Prop where
  ctx : Ctx s index pk
  input : s.getReg .x10 = W (prevInput k)
  out : 1 ≤ k → s.getReg .x12 = W (slotAddr (k - 1) - 8)
  payload : PayloadFrom s payload k
  done : 2 ≤ k → MemBits s (W regionAddr) (lowCat (topFun (tops x)) (k - 2))
  top : 1 ≤ k → MemBits s (W (slotAddr (k - 1) - 8)) (topFun (tops x) (k - 1))

/-- The root prefix grows by the low 192 bits of the next top. -/
theorem lowCat_extend (s : MachineState) (j : ℕ) (hj : j + 1 < 28) (c : ℕ → BitVec 256)
    (prev : MemBits s (W regionAddr) (lowCat c j))
    (next : MemBits s (W (slotAddr (j + 1) - 8)) (lo192 (c (j + 1)))) :
    MemBits s (W regionAddr) (lowCat c (j + 1)) := by
  rw [lowCat]
  apply (memBits_cast _ _ _ _).mpr
  apply memBits_append (by omega) prev
  have base : W regionAddr + BitVec.ofNat 64 (192 * (j + 1) / 8) = W (slotAddr (j + 1) - 8) := by
    rw [W_add]
    congr 1
    unfold slotAddr payloadAddr regionAddr
    omega
  rw [base]
  exact next

/-- The root prefix before chain `k`, from the invariant. -/
theorem lowCat_of_inv {s : MachineState} {x : graph.Assignment} {k : ℕ} (hk : k < 28)
    (inv : ChainsInv index payload pk s x k) (hk1 : 1 ≤ k) :
    MemBits s (W regionAddr) (lowCat (topFun (tops x)) (k - 1)) := by
  have next := lo_of_answer (inv.top hk1)
  rcases Nat.lt_or_ge k 2 with h1 | h2
  · obtain rfl : k = 1 := by omega
    simp only [Nat.sub_self] at next ⊢
    have e : W (slotAddr 0 - 8) = W regionAddr := by
      unfold slotAddr payloadAddr regionAddr; rfl
    rw [e] at next
    exact next
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [show j + 2 - 1 = j + 1 by omega]
    have hd := inv.done h2
    rw [show j + 2 - 2 = j by omega] at hd
    apply lowCat_extend s j (by omega) _ hd
    rw [show j + 2 - 1 = j + 1 by omega] at next
    exact next

/-- The value read at a disclosed node is the specification's decoded value. -/
theorem read_value (k : ℕ) (n : Name) (hn : graph.len n.fin = 192) (cursor : ℕ)
    (t : MachineState) (held : Holds t k (ofBits 192 (payload.drop cursor))) :
    Holds t k (ofBits (graph.len n.fin) ((payload.drop cursor).take (graph.len n.fin))) := by
  unfold Holds
  rw [hn]
  have take : ofBits 192 ((payload.drop cursor).take 192) = ofBits 192 (payload.drop cursor) := by
    simpa only [List.drop_zero] using
      ofBits_drop_take (payload.drop cursor) (cap := 192) (start := 0) (len := 192) (by decide)
  rw [take]
  exact held

/-! ## The steps from the disclosed position -/

/-- What the slot holds before level `t`, or the full top after the last level. -/
def HoldsAt (s : MachineState) (x : graph.Assignment) (k : Fin 28) (t : ℕ) : Prop :=
  if h : t < 32 then
    Holds s k ((Forest.trunc (x (prev k ⟨t, h⟩).fin)).cast (graph_len_fin (ci k ⟨t, h⟩)).symm)
  else MemBits s (W (slotAddr k - 8)) (tops x k)

theorem prev_succ (k : Fin 28) (t : Fin 32) (ht : t.val < 31) :
    prev k ⟨t.val + 1, by omega⟩ = cv k t := by
  simp [prev]

/-- The answer of level `t` is what the next level needs. -/
theorem holdsAt_succ {u : MachineState} {x : graph.Assignment} {k : Fin 28} {t : Fin 32}
    {v : BitVec (graph.len (ci k t).fin)} {y : BitVec hashBits}
    (answer : MemBits u (W (slotAddr k - 8)) y) :
    HoldsAt u (tripleUpdate x k t v y) k (t.val + 1) := by
  unfold HoldsAt
  by_cases h : t.val + 1 < 32
  · rw [dif_pos h]
    have e : prev k ⟨t.val + 1, h⟩ = cv k t := prev_succ k t (by omega)
    unfold Holds
    apply (memBits_cast _ _ _ _).mpr
    rw [e, trunc_tripleUpdate_cv]
    exact holds_of_answer k.isLt answer
  · rw [dif_neg h]
    have ht : t = 31 := Fin.ext (by have := t.isLt; omega)
    subst ht
    unfold tops
    rw [tripleUpdate_cv]
    apply (memBits_cast _ _ _ _).mpr
    apply (memBits_cast _ _ _ _).mpr
    apply (memBits_cast _ _ _ _).mpr
    apply (memBits_cast _ _ _ _).mpr
    exact answer

/-- Levels `t` to `31` of chain `k`, above the disclosed level. -/
theorem steps_refines (k : Fin 28) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest' cursor : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      StepInv index payload pk u y k 32 → MemBits u (W (slotAddr k - 8)) (tops y k) →
      Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, cursor)) c) :
    ∀ (n t : ℕ), 32 - t = n → t ≤ 32 → RiscvUpperForest.ForestVerifier.pos index k < t →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel : ℕ),
      StepInv index payload pk s x k t → HoldsAt s x k t →
      Riscv.CodeAt s s.pc (List.replicate (32 - t) .ECALL ++ tail) →
      (32 - t) + rest' ≤ fuel →
      Riscv.Refines fuel s
        (runNodes' index payload ((List.range' t (32 - t)).flatMap (tripleN k)) x cursor >>= K)
        ((32 - t) + c) := by
  intro n
  induction n with
  | zero =>
    intro t ht _ _ s x fuel inv held located bound
    have h32 : t = 32 := by omega
    subst h32
    simp only [Nat.sub_self, List.range'_zero, List.flatMap_nil, List.nil_append, runNodes',
      pure_bind, List.replicate_zero, Nat.zero_add] at located bound ⊢
    unfold HoldsAt at held
    rw [dif_neg (by omega)] at held
    exact continuation s x inv held located fuel bound
  | succ n ih =>
    intro t hn ht hp s x fuel inv held located bound
    have ht' : t < 32 := by omega
    have hsucc : 32 - t = (32 - (t + 1)) + 1 := by omega
    rw [hsucc] at located bound ⊢
    rw [List.range'_succ, List.flatMap_cons, runNodes'_append, bind_assoc]
    have triple : tripleN k t = [ci k ⟨t, ht'⟩, ch k ⟨t, ht'⟩, cv k ⟨t, ht'⟩] := by
      simp [tripleN, ht']
    rw [triple]
    rw [List.replicate_succ, List.cons_append] at located
    rw [show 32 - (t + 1) + 1 + c = 1 + (32 - (t + 1) + c) by omega]
    unfold HoldsAt at held
    rw [dif_pos ht'] at held
    apply step_refines index payload pk k ⟨t, ht'⟩
      (tail := List.replicate (32 - (t + 1)) .ECALL ++ tail)
      (fun r => runNodes' index payload ((List.range' (t + 1) (32 - (t + 1))).flatMap (tripleN k))
        r.1 r.2 >>= K)
      (32 - (t + 1) + c) (32 - (t + 1) + rest') cursor cursor s x fuel _
      (triple_run_step index payload k ⟨t, ht'⟩ hp x cursor) inv held located (by omega)
    intro u y inv' answer located' left hleft
    exact ih (t + 1) (by omega) (by omega) (by omega) u _ left inv' (holdsAt_succ answer)
      located' (by omega)

/-! ## A chain from its landing point -/

/-- Chain `k` from the step of its disclosed position to its top, at `32 - p` cycles: the
continuation starts between chains, on the code after the table. -/
theorem table_refines (k : Fin 28) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      ChainsInv index payload pk u y (k.val + 1) → Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, 192 * k.val + 192)) c)
    (u : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : StepInv index payload pk u x k (RiscvUpperForest.ForestVerifier.pos index k))
    (held : Holds u k (ofBits 192 (payload.drop (192 * k.val))))
    (located : Riscv.CodeAt u u.pc
      (List.replicate (32 - RiscvUpperForest.ForestVerifier.pos index k) .ECALL ++ tail))
    (bound : (32 - RiscvUpperForest.ForestVerifier.pos index k) + rest' ≤ fuel) :
    Riscv.Refines fuel u (runNodes' index payload (chainNodes k) x (192 * k.val) >>= K)
      ((32 - RiscvUpperForest.ForestVerifier.pos index k) + c) := by
  have hp := pos_le index k
  have hs := slot_bounds k k.isLt
  set p := RiscvUpperForest.ForestVerifier.pos index k with hpdef
  have hp32 : p < 32 := by omega
  -- the specification up to the disclosed level is pure
  obtain ⟨x', run, frame⟩ := prefix_run index payload k p le_rfl x (192 * k.val)
  have nodes : chainNodes k = (src k :: (List.range p).flatMap (tripleN k)) ++
      (tripleN k p ++ (List.range' (p + 1) (32 - (p + 1))).flatMap (tripleN k)) := by
    rw [chainNodes_eq, range_split p (by omega), List.flatMap_append, List.cons_append,
      show 32 - p = (32 - (p + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons]
  rw [nodes, runNodes'_append, run, bind_assoc, pure_bind]
  dsimp only
  -- the disclosed level
  have inv'' : StepInv index payload pk u x' k p := by
    refine ⟨inv.ctx, inv.input, inv.out, inv.payload, ?_⟩
    intro hk1
    have e : lowCat (topFun (tops x')) (k.val - 1) = lowCat (topFun (tops x)) (k.val - 1) := by
      apply lowCat_congr
      intro i hi
      unfold topFun tops
      split_ifs with hi28
      · rw [frame ⟨i, hi28⟩ (by intro e; have := congrArg Fin.val e; simp at this; omega)]
      · rfl
    rw [e]
    exact inv.done hk1
  have triple : tripleN k p = [ci k ⟨p, hp32⟩, ch k ⟨p, hp32⟩, cv k ⟨p, hp32⟩] := by
    simp [tripleN, hp32]
  rw [triple, runNodes'_append, bind_assoc]
  rw [show 32 - p = (32 - (p + 1)) + 1 by omega] at located bound ⊢
  rw [List.replicate_succ, List.cons_append] at located
  rw [show 32 - (p + 1) + 1 + c = 1 + (32 - (p + 1) + c) by omega]
  have held' : Holds u k (ofBits (graph.len (ci k ⟨p, hp32⟩).fin)
      ((payload.drop (192 * k.val)).take (graph.len (ci k ⟨p, hp32⟩).fin))) :=
    read_value payload k _ (graph_len_fin _) _ u held
  apply step_refines index payload pk k ⟨p, hp32⟩
    (tail := List.replicate (32 - (p + 1)) .ECALL ++ tail)
    (fun r => runNodes' index payload ((List.range' (p + 1) (32 - (p + 1))).flatMap (tripleN k))
      r.1 r.2 >>= K)
    (32 - (p + 1) + c) (32 - (p + 1) + rest') (192 * k.val) (192 * k.val + 192) u x' fuel _
    (triple_run_read index payload k ⟨p, hp32⟩ rfl x' (192 * k.val)) inv'' held' located
    (by omega)
  intro v y invV answer locatedV left hleft
  -- the remaining levels
  apply steps_refines index payload pk k tail K c rest' (192 * k.val + 192) ?_
    (32 - (p + 1)) (p + 1) rfl (by omega) (by omega) v _ left invV (holdsAt_succ answer)
    locatedV hleft
  intro w z invW topW locatedW left' hleft'
  apply continuation w z ?_ locatedW left' hleft'
  refine ⟨invW.ctx, ?_, ?_, invW.payload, ?_, ?_⟩
  · rw [invW.input]
    unfold prevInput
    rw [if_neg (by omega)]
    show W _ = W _
    congr 1
  · intro _
    rw [invW.out, show k.val + 1 - 1 = k.val by omega]
  · intro h2
    rw [show k.val + 1 - 2 = k.val - 1 by omega]
    exact invW.done (by omega)
  · intro _
    rw [show k.val + 1 - 1 = k.val by omega]
    unfold topFun
    rw [dif_pos k.isLt]
    exact topW

/-! ## The prologue and the jump -/

/-- Block `q`'s prologue: the pointers are set and control jumps to the step of the first chain's
disclosed position in the selected copy or table, at four cycles. -/
theorem prologue_refines (q : ℕ) (hq : q < 16) (rest : Code) (s : MachineState)
    (x : graph.Assignment) (inv : ChainsInv index payload pk s x (firstChain q))
    (located : Riscv.CodeAt s s.pc (prologue q ++ rest))
    {fuel : ℕ} {Q : OracleComp Spec (Option Bool)} {c : ℕ}
    (continuation : ∀ u : MachineState,
      StepInv index payload pk u x ⟨firstChain q, firstChain_lt q hq⟩
        (RiscvUpperForest.ForestVerifier.pos index ⟨firstChain q, firstChain_lt q hq⟩) →
      Holds u (firstChain q) (ofBits 192 (payload.drop (192 * firstChain q))) →
      u.pc = W (landing0 q - dispatch index q) → Riscv.Refines fuel u Q c) :
    Riscv.Refines (4 + fuel) s Q (4 + c) := by
  have hk := firstChain_lt q hq
  have hs := slot_bounds (firstChain q) hk
  rw [prologue_parts, List.append_assoc] at located
  have ready := prologueLinear_ready s q hq inv.input
  have E := prologueLinear_effect s q hq inv.input
  set b := (prologueLinear q).foldl execInstrBr s with hb
  have bLocated : Riscv.CodeAt b b.pc ([Instr.JALR .x0 .x28 (imm12 (jumpImm q))] ++ rest) := by
    rw [Riscv.linear_fold_pc s _ ready, prologueLinear_length]
    have h := located.append_right
    rw [prologueLinear_length] at h
    exact h.code_eq (Riscv.fold_code s _)
  rw [show 4 + fuel = (prologueLinear q).length + (fuel + 1) by rw [prologueLinear_length]; omega,
    show 4 + c = (prologueLinear q).length + (c + 1) by rw [prologueLinear_length]; omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hb]
  have fetchJ := bLocated.head
  apply Riscv.Refines.branch fetchJ rfl (fun h => nomatch h) (jalr_transition b _ fetchJ)
  have hl : (s.getHalfword (W (laneAddr q))).toNat = laneBaseOf (laneGroup q) - dispatch index q :=
    inv.ctx.lanes ⟨q, hq⟩
  have hx28 : (b.getReg .x28).toNat = laneBaseOf (laneGroup q) - dispatch index q := by
    rw [E.target, BitVec.toNat_setWidth, hl, Nat.mod_eq_of_lt]
    have := laneBaseOf_bounds (laneGroup q)
    omega
  rw [jump_target index q hq _ hx28]
  set u := b.setPC (W (landing0 q - dispatch index q)) with hu
  have uRegs : ∀ r, u.getReg r = b.getReg r := fun r => by rw [hu]; simp
  have uMem : ∀ addr, u.getMem addr = b.getMem addr := fun addr => by rw [hu]; simp
  have frame : SlotFrame s u (firstChain q) := by
    intro addr _
    rw [uMem, E.mem]
  apply continuation u ?_ ?_ rfl
  · refine ⟨inv.ctx.frame (firstChain q) hk (fun r hr => ?_) frame
      (by rw [hu, MachineState.code_setPC, E.code]), ?_, ?_, ?_, ?_⟩
    · obtain ⟨h10, h12, h28⟩ := notCtx_of_prologue r hr
      rw [uRegs, E.regs r h10 h12 h28]
    · rw [uRegs, E.input]
    · rw [uRegs, E.out]
    · intro j hj hj28
      apply memBits_of_mem_eq (show u.mem = s.mem from funext fun a => (uMem a).trans (E.mem a))
      exact inv.payload j (Nat.le_of_succ_le hj) hj28
    · intro hk1
      apply memBits_of_mem_eq (show u.mem = s.mem from funext fun a => (uMem a).trans (E.mem a))
      exact lowCat_of_inv index payload pk hk inv hk1
  · apply memBits_of_mem_eq (show u.mem = s.mem from funext fun a => (uMem a).trans (E.mem a))
    exact inv.payload (firstChain q) le_rfl hk

/-- The switch before chain `k` of a pair: the pointers move to its slot, at two cycles. -/
theorem switch_refines (k : ℕ) (hk : k < 28) (hk0 : k ≠ 0) (rest : Code) (s : MachineState)
    (x : graph.Assignment) (inv : ChainsInv index payload pk s x k)
    (located : Riscv.CodeAt s s.pc (switch ++ rest))
    {fuel : ℕ} {Q : OracleComp Spec (Option Bool)} {c : ℕ}
    (continuation : ∀ u : MachineState,
      StepInv index payload pk u x ⟨k, hk⟩ (RiscvUpperForest.ForestVerifier.pos index ⟨k, hk⟩) →
      Holds u k (ofBits 192 (payload.drop (192 * k))) → Riscv.CodeAt u u.pc rest →
      Riscv.Refines fuel u Q c) :
    Riscv.Refines (2 + fuel) s Q (2 + c) := by
  have hs := slot_bounds k hk
  have ready := switch_ready s
  have E := switch_effect s k hk hk0 inv.input
  set u := switch.foldl execInstrBr s with hu
  rw [show 2 + fuel = switch.length + fuel by rw [switch_length],
    show 2 + c = switch.length + c by rw [switch_length]]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hu]
  have uLocated : Riscv.CodeAt u u.pc rest := by
    rw [Riscv.linear_fold_pc s _ ready, switch_length]
    have h := located.append_right
    rw [switch_length] at h
    exact h.code_eq (Riscv.fold_code s _)
  have frame : SlotFrame s u k := by
    intro addr _
    rw [E.mem]
  apply continuation u ?_ ?_ uLocated
  · refine ⟨inv.ctx.frame k hk (fun r hr => ?_) frame (Riscv.fold_code s _), E.input, E.out,
      ?_, ?_⟩
    · obtain ⟨h10, h12, -⟩ := notCtx_of_prologue r hr
      rw [E.regs r h10 h12]
    · intro j hj hj28
      apply memBits_of_mem_eq (funext E.mem)
      exact inv.payload j (Nat.le_of_succ_le hj) hj28
    · intro hk1
      apply memBits_of_mem_eq (funext E.mem)
      exact lowCat_of_inv index payload pk hk inv hk1
  · apply memBits_of_mem_eq (funext E.mem)
    exact inv.payload k le_rfl hk

/-! ## The digits of a block -/

theorem pos_eq_digit (k : ℕ) (hk : k < 28) :
    RiscvUpperForest.ForestVerifier.pos index ⟨k, hk⟩ = 31 - digit index.val k :=
  Forest.fixedPositions_val index ⟨k, hk⟩

/-- The landing address of a pair is the step of the first chain's position in copy `dB`. -/
theorem pair_landing (q : ℕ) (hq : q < 12) :
    landing0 q - dispatch index q =
      copyStart q (coarseDigit index q) +
        4 * RiscvUpperForest.ForestVerifier.pos index ⟨2 * q, by omega⟩ := by
  have hfc : firstChain q = 2 * q := by unfold firstChain; rw [if_pos hq]
  have hd := digit_lt_32' index.val (2 * q)
  have hc := coarseDigit_lt index q
  rw [pos_eq_digit index (2 * q) (by omega)]
  unfold dispatch landing0 copyStart copiesStart indexLength
  rw [hfc, if_pos hq]
  omega

/-- The second chain's table in copy `dB` has exactly its steps. -/
theorem pair_second_steps (q : ℕ) (hq : q < 12) :
    coarseDigit index q + 1 =
      32 - RiscvUpperForest.ForestVerifier.pos index ⟨2 * q + 1, by omega⟩ := by
  have hd := digit_lt_32' index.val (2 * q + 1)
  rw [pos_eq_digit index (2 * q + 1) (by omega)]
  unfold coarseDigit
  rw [if_pos hq]
  omega

/-- The landing address of a single is the step of its position in its table. -/
theorem single_landing (q : ℕ) (hq : 12 ≤ q) (hq' : q < 16) :
    landing0 q - dispatch index q =
      singleTableStart (q - 12) +
        4 * RiscvUpperForest.ForestVerifier.pos index ⟨12 + q, by omega⟩ := by
  have hfc : firstChain q = 12 + q := by unfold firstChain; rw [if_neg (by omega)]
  have hd := digit_lt_32' index.val (12 + q)
  rw [pos_eq_digit index (12 + q) (by omega)]
  unfold dispatch landing0 coarseDigit
  rw [hfc, if_neg (by omega), if_neg (by omega), Nat.mul_zero, Nat.add_zero]
  omega

/-! ## The whole block -/

/-- The code the continuation of block `q` starts on: the next prologue, or the root. -/
def nextCode (q : ℕ) : Code := if q + 1 < 16 then prologue (q + 1) else root ++ decision

/-- The cycles of block `q`. -/
def blockCycles (q : ℕ) : ℕ :=
  if h : q < 12 then
    6 + (32 - RiscvUpperForest.ForestVerifier.pos index ⟨2 * q, by omega⟩) +
      (32 - RiscvUpperForest.ForestVerifier.pos index ⟨2 * q + 1, by omega⟩)
  else if h' : q < 16 then 4 + (32 - RiscvUpperForest.ForestVerifier.pos index ⟨12 + q, by omega⟩)
  else 0

/-- The nodes of block `q`. -/
def blockNodes (q : ℕ) : List Name :=
  if h : q < 12 then chainNodes ⟨2 * q, by omega⟩ ++ chainNodes ⟨2 * q + 1, by omega⟩
  else if h' : q < 16 then chainNodes ⟨12 + q, by omega⟩ else []

theorem firstChain_succ (q : ℕ) (hq : q < 16) : firstChain (q + 1) =
    if q < 12 then 2 * q + 2 else 12 + q + 1 := by
  unfold firstChain; split_ifs <;> omega

/-- A pair block: the prologue, the first chain, the switch and the second chain. -/
theorem pair_refines (q : ℕ) (hq : q < 12)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      ChainsInv index payload pk u y (2 * q + 2) →
      (∃ junk, Riscv.CodeAt u u.pc (prologue (q + 1) ++ junk)) →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, 192 * (2 * q + 2))) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : ChainsInv index payload pk s x (2 * q))
    (located : ∃ junk, Riscv.CodeAt s s.pc (prologue q ++ junk))
    (bound : blockCycles index q + rest' ≤ fuel) :
    Riscv.Refines fuel s (runNodes' index payload (blockNodes q) x (192 * (2 * q)) >>= K)
      (blockCycles index q + c) := by
  obtain ⟨junk, located⟩ := located
  have hq16 : q < 16 := by omega
  have hfc : firstChain q = 2 * q := by unfold firstChain; rw [if_pos hq]
  unfold blockCycles at bound ⊢
  rw [dif_pos hq] at bound ⊢
  unfold blockNodes
  rw [dif_pos hq, runNodes'_append, bind_assoc]
  set kA : Fin 28 := ⟨2 * q, by omega⟩ with hkA
  set kB : Fin 28 := ⟨2 * q + 1, by omega⟩ with hkB
  have hpA := pos_le index kA
  have hpB := pos_le index kB
  have invA : ChainsInv index payload pk s x (firstChain q) := by rw [hfc]; exact inv
  rw [show fuel = 4 + (fuel - 4) by omega,
    show 6 + (32 - RiscvUpperForest.ForestVerifier.pos index kA) +
      (32 - RiscvUpperForest.ForestVerifier.pos index kB) + c =
      4 + ((32 - RiscvUpperForest.ForestVerifier.pos index kA) +
        (2 + ((32 - RiscvUpperForest.ForestVerifier.pos index kB) + c))) by omega]
  apply prologue_refines index payload pk q hq16 junk s x invA located
  intro u invU heldU pcU
  have hkF : (⟨firstChain q, firstChain_lt q hq16⟩ : Fin 28) = kA := Fin.ext hfc
  rw [hkF] at invU
  rw [hfc] at heldU
  -- locate the copy
  obtain ⟨rest, copyLoc⟩ := copy_located u invU.ctx.code q (coarseDigit index q) hq (coarseDigit_lt index q)
  have copyLoc' : Riscv.CodeAt u (W (copyStart q (coarseDigit index q)))
      (List.replicate 32 .ECALL ++ (switch ++ (List.replicate (coarseDigit index q + 1) .ECALL ++
        (prologue (q + 1) ++ (List.replicate (25 - coarseDigit index q) nop ++ rest))))) := by
    simpa only [copyCode, List.append_assoc] using copyLoc
  have landed := landing_code copyLoc' (RiscvUpperForest.ForestVerifier.pos index kA) (by omega)
  rw [← pair_landing index q hq, ← pcU] at landed
  -- the first chain
  apply table_refines index payload pk kA _
    (fun r => runNodes' index payload (chainNodes kB) r.1 r.2 >>= K)
    (2 + ((32 - RiscvUpperForest.ForestVerifier.pos index kB) + c))
    (2 + ((32 - RiscvUpperForest.ForestVerifier.pos index kB) + rest')) ?_ u x (fuel - 4) invU heldU
    landed (by omega)
  intro v y invV locatedV left hleft
  dsimp only
  rw [show 192 * kA.val + 192 = 192 * kB.val by simp [hkA, hkB]; ring]
  -- the switch
  rw [show left = 2 + (left - 2) by omega]
  apply switch_refines index payload pk kB.val kB.isLt (by simp [hkB]) _ v y invV locatedV
  intro w invW heldW locatedW
  rw [pair_second_steps index q hq] at locatedW
  -- the second chain
  apply table_refines index payload pk kB _ K c rest' ?_ w y (left - 2) invW heldW locatedW (by omega)
  intro z t invZ locatedZ left' hleft'
  have e : kB.val + 1 = 2 * q + 2 := by simp [hkB]
  have e' : 192 * kB.val + 192 = 192 * (2 * q + 2) := by simp [hkB]; ring
  rw [e] at invZ
  rw [e']
  exact continuation z t invZ ⟨_, locatedZ⟩ left' hleft'

/-- A single block: the prologue and the chain. -/
theorem single_refines (q : ℕ) (hq : 12 ≤ q) (hq' : q < 16)
    (K : graph.Assignment × ℕ → OracleComp Spec (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      ChainsInv index payload pk u y (12 + q + 1) →
      (∃ junk, Riscv.CodeAt u u.pc (nextCode q ++ junk)) →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, 192 * (12 + q + 1))) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : ChainsInv index payload pk s x (12 + q))
    (located : ∃ junk, Riscv.CodeAt s s.pc (prologue q ++ junk))
    (bound : blockCycles index q + rest' ≤ fuel) :
    Riscv.Refines fuel s (runNodes' index payload (blockNodes q) x (192 * (12 + q)) >>= K)
      (blockCycles index q + c) := by
  obtain ⟨junk, located⟩ := located
  have hfc : firstChain q = 12 + q := by unfold firstChain; rw [if_neg (by omega)]
  unfold blockCycles at bound ⊢
  rw [dif_neg (by omega), dif_pos hq'] at bound ⊢
  unfold blockNodes
  rw [dif_neg (by omega), dif_pos hq']
  set k : Fin 28 := ⟨12 + q, by omega⟩ with hk
  have hp := pos_le index k
  have invA : ChainsInv index payload pk s x (firstChain q) := by rw [hfc]; exact inv
  rw [show fuel = 4 + (fuel - 4) by omega, Nat.add_assoc]
  apply prologue_refines index payload pk q hq' junk s x invA located
  intro u invU heldU pcU
  have hkF : (⟨firstChain q, firstChain_lt q hq'⟩ : Fin 28) = k := Fin.ext hfc
  rw [hkF] at invU
  rw [hfc] at heldU
  obtain ⟨rest, tableLoc⟩ := single_located u invU.ctx.code (q - 12) (by omega)
  have landed := landing_code tableLoc (RiscvUpperForest.ForestVerifier.pos index k) (by omega)
  rw [← single_landing index q hq hq', ← pcU] at landed
  apply table_refines index payload pk k _ K c rest' ?_ u x (fuel - 4) invU heldU landed (by omega)
  intro z t invZ locatedZ left' hleft'
  have e : k.val + 1 = 12 + q + 1 := by simp [hk]
  have e' : 192 * k.val + 192 = 192 * (12 + q + 1) := by simp [hk]; ring
  rw [e] at invZ
  rw [e']
  have hnext : singleTail (q - 12) = nextCode q := by
    unfold singleTail nextCode
    split_ifs <;> first | rfl | omega | (congr 1; omega)
  rw [hnext] at locatedZ
  exact continuation z t invZ ⟨_, locatedZ⟩ left' hleft'

end OptimalOTS.Riscv2Program
