import Submissions.UpperRiscv.Master
import Submissions.UpperRiscv.Semantics
import Submissions.UpperRiscv.GScheme

/-!
# Reconstruction and verification under the lazy random oracle

Support-level descriptions of the runs of `Graph.reconstruct`, `index` and `GScheme.verify`:
whatever the oracle answers, the final cache contains the answers to every query made, and the
computed assignment satisfies the reconstruction equations with respect to that cache.

Also the two round trips between `Graph.encode` and `Graph.decode`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


/-! ## Bit strings -/

theorem testBit_foldr_bits (l : List Bool) (i : ℕ) :
    (l.foldr (fun (b : Bool) (acc : ℕ) => b.toNat + 2 * acc) 0).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases i with _ | i
    · rw [Nat.testBit_zero]
      cases b <;> simp [Nat.add_mul_mod_self_left]
    · rw [Nat.testBit_succ, List.getD_cons_succ, ← ih i]
      congr 1
      cases b <;> simp
      omega

theorem length_toBits {n : ℕ} (x : BitVec n) : (toBits x).length = n := List.length_ofFn

theorem ofBits_toBits {n : ℕ} (x : BitVec n) : ofBits n (toBits x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofBits, BitVec.getLsbD_ofNat, toBits]
  rw [testBit_foldr_bits]
  simp [hi, List.getD_eq_getElem?_getD]

theorem toBits_ofBits {n : ℕ} (l : List Bool) (hl : l.length = n) : toBits (ofBits n l) = l := by
  apply List.ext_getElem
  · rw [length_toBits, hl]
  · intro i h1 h2
    simp only [toBits, List.getElem_ofFn, ofBits, BitVec.getLsbD_ofNat]
    rw [testBit_foldr_bits, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rw [length_toBits] at h1
    simp [h1]

/-! ## Chunks of a list along a sorted index list -/

theorem flatMap_congr_mem {α β : Type*} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      ih fun a ha => h a (List.mem_cons_of_mem _ ha)]

/-- The offset of `v` in the concatenation of chunks of lengths `len` along a sorted list. -/
def chunkOff {n : ℕ} (len : Fin n → ℕ) (L : List (Fin n)) (v : Fin n) : ℕ :=
  ((L.filter fun w => decide (w < v)).map len).sum

theorem chunkOff_cons_self {n : ℕ} (len : Fin n → ℕ) (a : Fin n) (L : List (Fin n))
    (hL : ∀ w ∈ L, a < w) : chunkOff len (a :: L) a = 0 := by
  unfold chunkOff
  have h : ((a :: L).filter fun w => decide (w < a)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · simp
    · simpa using le_of_lt (hL w hw)
  rw [h]; rfl

theorem chunkOff_cons_of_lt {n : ℕ} (len : Fin n → ℕ) (a : Fin n) (L : List (Fin n))
    {v : Fin n} (hv : a < v) : chunkOff len (a :: L) v = len a + chunkOff len L v := by
  unfold chunkOff
  simp [hv]

theorem chunkOff_add_le {n : ℕ} (len : Fin n → ℕ) :
    ∀ (L : List (Fin n)), L.Pairwise (· < ·) → ∀ v ∈ L,
      chunkOff len L v + len v ≤ (L.map len).sum := by
  intro L
  induction L with
  | nil => intro _ v hv; simp at hv
  | cons a L ih =>
    intro hL v hv
    rw [List.pairwise_cons] at hL
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hv with rfl | hv
    · rw [chunkOff_cons_self len v L hL.1]
      omega
    · rw [chunkOff_cons_of_lt len a L (hL.1 v hv)]
      have := ih hL.2 v hv
      omega

theorem flatMap_chunks {n : ℕ} (len : Fin n → ℕ) :
    ∀ (L : List (Fin n)), L.Pairwise (· < ·) → ∀ (l : List Bool), l.length = (L.map len).sum →
      L.flatMap (fun v => (l.drop (chunkOff len L v)).take (len v)) = l := by
  intro L
  induction L with
  | nil =>
    intro _ l hl
    simp at hl
    subst hl
    rfl
  | cons a L ih =>
    intro hL l hl
    rw [List.pairwise_cons] at hL
    rw [List.map_cons, List.sum_cons] at hl
    rw [List.flatMap_cons, chunkOff_cons_self len a L hL.1, List.drop_zero]
    have h2 : L.flatMap (fun v => (l.drop (chunkOff len (a :: L) v)).take (len v)) =
        L.flatMap (fun v => ((l.drop (len a)).drop (chunkOff len L v)).take (len v)) := by
      refine flatMap_congr_mem fun v hv => ?_
      rw [chunkOff_cons_of_lt len a L (hL.1 v hv), List.drop_drop]
    rw [h2, ih hL.2 (l.drop (len a)) (by rw [List.length_drop]; omega), List.take_append_drop]

namespace Dag.Graph

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

/-- The reconstruction equation at a single node. -/
def ReconEqAt (d : Cache) (A : Finset (Fin G.size)) (given y : G.Assignment)
    (v : Fin G.size) : Prop :=
  (v ∈ A → y v = given v) ∧
    (v ∉ A → ¬ G.Visited A v → y v = 0) ∧
    (v ∉ A → G.Visited A v →
      (∀ p hp hl, G.kind v = .hash p hp hl →
        ∃ w, d ⟨G.len p, y p⟩ = some w ∧ y v = w.cast hl.symm) ∧
      (∀ ps hlt f hf, G.kind v = .det ps hlt f hf → y v = f y) ∧
      (G.kind v = .source → y v = 0))

/-- `y` satisfies the reconstruction equations from the values `given` on `A`, with every hash
answer recorded in the cache `d`. -/
def ReconEqs (d : Cache) (A : Finset (Fin G.size)) (given y : G.Assignment) : Prop :=
  ∀ v, (v ∈ A → y v = given v) ∧
    (v ∉ A → ¬ G.Visited A v → y v = 0) ∧
    (v ∉ A → G.Visited A v →
      (∀ p hp hl, G.kind v = .hash p hp hl →
        ∃ w, d ⟨G.len p, y p⟩ = some w ∧ y v = w.cast hl.symm) ∧
      (∀ ps hlt f hf, G.kind v = .det ps hlt f hf → y v = f y) ∧
      (G.kind v = .source → y v = 0))

theorem ReconEqAt.mono {d d' : Cache} (h : Cache.Sub d d') {A : Finset (Fin G.size)}
    {given y : G.Assignment} {v : Fin G.size} (he : G.ReconEqAt d A given y v) :
    G.ReconEqAt d' A given y v := by
  obtain ⟨h1, h2, h3⟩ := he
  refine ⟨h1, h2, fun hA hV => ?_⟩
  obtain ⟨h31, h32, h33⟩ := h3 hA hV
  refine ⟨fun p hp hl hk => ?_, h32, h33⟩
  obtain ⟨w, hw, hy⟩ := h31 p hp hl hk
  exact ⟨w, h _ _ hw, hy⟩

/-- The equation at `v` only looks at the values at nodes `≤ v`. -/
theorem ReconEqAt.congr {d : Cache} {A : Finset (Fin G.size)} {given y y' : G.Assignment}
    {v : Fin G.size} (h : ∀ u, u ≤ v → y' u = y u) (he : G.ReconEqAt d A given y v) :
    G.ReconEqAt d A given y' v := by
  obtain ⟨h1, h2, h3⟩ := he
  have hv : y' v = y v := h v le_rfl
  refine ⟨fun hA => by rw [hv]; exact h1 hA, fun hA hV => by rw [hv]; exact h2 hA hV,
    fun hA hV => ?_⟩
  obtain ⟨h31, h32, h33⟩ := h3 hA hV
  refine ⟨fun p hp hl hk => ?_, fun ps hlt f hf hk => ?_, fun hk => by rw [hv]; exact h33 hk⟩
  · obtain ⟨w, hw, hyw⟩ := h31 p hp hl hk
    refine ⟨w, ?_, by rw [hv]; exact hyw⟩
    rw [h p hp.le]; exact hw
  · rw [hv, h32 ps hlt f hf hk]
    exact hf y y' fun w hw => (h w (hlt w hw).le).symm

end Dag.Graph

/-! ## Support of a hash query -/

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- A hash query records its answer in the cache. -/
theorem hash_support {k : ℕ} (u : BitVec k) (c : Cache) :
    ∀ p ∈ support (run (hash u) c), Cache.Sub c p.2 ∧ p.2 ⟨k, u⟩ = some p.1 := by
  intro p hp
  have h : hash u = liftM (Spec.query (.inr ⟨k, u⟩)) >>= pure := (bind_pure _).symm
  rw [h, run_query_bind] at hp
  simp only [run_pure] at hp
  rw [support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨v, c'⟩, hv, hp⟩ := hp
  rw [support_pure, Set.mem_singleton_iff] at hp
  subst hp
  rcases hc : c ⟨k, u⟩ with _ | w
  · rw [oracleImpl_run_inr_none hc, support_bind] at hv
    simp only [Set.mem_iUnion] at hv
    obtain ⟨w, -, hw⟩ := hv
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨Cache.sub_cacheQuery_of_none hc _, QueryCache.cacheQuery_self ..⟩
  · rw [oracleImpl_run_inr_some hc, support_pure] at hv
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨Cache.Sub.refl _, hc⟩

namespace Dag.Graph

variable (G : Graph)

/-- Support of evaluating one node (with source value `0`). -/
theorem evalNode_support (x : G.Assignment) (v : Fin G.size) (c : Cache) :
    ∀ p ∈ support (run (G.evalNode x v (pure 0)) c),
      Cache.Sub c p.2 ∧
      (∀ q hq hl, G.kind v = .hash q hq hl →
        ∃ w, p.2 ⟨G.len q, x q⟩ = some w ∧ p.1 = w.cast hl.symm) ∧
      (∀ ps hlt f hf, G.kind v = .det ps hlt f hf → p.1 = f x) ∧
      (G.kind v = .source → p.1 = 0) := by
  unfold evalNode
  generalize G.kind v = k
  cases k with
  | source =>
    intro p hp
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c, (fun _ _ _ h => nomatch h), (fun _ _ _ _ h => nomatch h),
      fun _ => rfl⟩
  | det ps hlt f hf =>
    intro p hp
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨Cache.Sub.refl c, (fun _ _ _ h => nomatch h), fun _ _ _ _ h => ?_,
      (fun h => nomatch h)⟩
    cases h
    rfl
  | hash q hq hl =>
    intro p hp
    rw [run_map, support_map, Set.mem_image] at hp
    obtain ⟨⟨w, c'⟩, hw, rfl⟩ := hp
    obtain ⟨hsub, hc'⟩ := hash_support _ c _ hw
    dsimp only at hsub hc' ⊢
    refine ⟨hsub, fun q' hq' hl' h => ?_, (fun _ _ _ _ h => nomatch h), (fun h => nomatch h)⟩
    cases h
    exact ⟨w, hc', rfl⟩

/-- One step of `reconstruct`. -/
def reconStep (A : Finset (Fin G.size)) (given : G.Assignment) (x : G.Assignment)
    (v : Fin G.size) : OracleComp Spec G.Assignment :=
  if v ∈ A then pure (Function.update x v (given v))
  else if G.Visited A v then Function.update x v <$> G.evalNode x v (pure 0)
  else pure (Function.update x v 0)

theorem reconstruct_eq_foldlM (A : Finset (Fin G.size)) (given : G.Assignment) :
    G.reconstruct A given =
      (List.finRange G.size).foldlM (G.reconStep A given) (fun _ => 0) := rfl

theorem reconStep_support (A : Finset (Fin G.size)) (given : G.Assignment) (x : G.Assignment)
    (a : Fin G.size) (c : Cache) :
    ∀ p ∈ support (run (G.reconStep A given x a) c),
      Cache.Sub c p.2 ∧ (∀ w, w ≠ a → p.1 w = x w) ∧ G.ReconEqAt p.2 A given p.1 a := by
  intro p hp
  unfold reconStep at hp
  by_cases hA : a ∈ A
  · rw [if_pos hA, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨Cache.Sub.refl c, fun w hw => Function.update_of_ne hw _ _, ?_⟩
    exact ⟨fun _ => Function.update_self .., fun h => absurd hA h, fun h => absurd hA h⟩
  · rw [if_neg hA] at hp
    by_cases hV : G.Visited A a
    · rw [if_pos hV, run_map, support_map, Set.mem_image] at hp
      obtain ⟨⟨y, c'⟩, hy, rfl⟩ := hp
      obtain ⟨hsub, hhash, hdet, hsrc⟩ := G.evalNode_support x a c ⟨y, c'⟩ hy
      dsimp only at hsub hhash hdet hsrc ⊢
      refine ⟨hsub, fun w hw => Function.update_of_ne hw _ _, ?_⟩
      refine ⟨fun h => absurd h hA, fun _ h => absurd hV h, fun _ _ => ⟨?_, ?_, ?_⟩⟩
      · intro p hp hl hk
        obtain ⟨w, hw, hyw⟩ := hhash p hp hl hk
        refine ⟨w, ?_, ?_⟩
        · rw [Function.update_of_ne (ne_of_lt hp)]; exact hw
        · rw [Function.update_self]; exact hyw
      · intro ps hlt f hf hk
        rw [Function.update_self, hdet ps hlt f hf hk]
        exact hf x _ fun w hw => (Function.update_of_ne (ne_of_lt (hlt w hw)) _ _).symm
      · intro hk
        rw [Function.update_self]
        exact hsrc hk
    · rw [if_neg hV, run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨Cache.Sub.refl c, fun w hw => Function.update_of_ne hw _ _, fun h => absurd h hA,
        fun _ _ => Function.update_self .., fun _ h => absurd h hV⟩

/-- Folding the reconstruction step over an increasing list: the equations hold at the nodes of
the list and every other node is still `0`. -/
theorem foldlM_reconStep_support (A : Finset (Fin G.size)) (given : G.Assignment) (c : Cache)
    (l : List (Fin G.size)) (hl : l.Pairwise (· < ·)) :
    ∀ p ∈ support (run (l.foldlM (G.reconStep A given) (fun _ => 0)) c),
      Cache.Sub c p.2 ∧ (∀ v ∈ l, G.ReconEqAt p.2 A given p.1 v) ∧
        (∀ v, v ∉ l → p.1 v = 0) := by
  induction l using List.reverseRecOn with
  | nil =>
    intro p hp
    rw [List.foldlM_nil, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c, fun v hv => by simp at hv, fun v _ => rfl⟩
  | append_singleton l a ih =>
    rw [List.pairwise_append] at hl
    obtain ⟨hl, -, hla⟩ := hl
    have hla' : ∀ v ∈ l, v < a := fun v hv => hla v hv a (List.mem_singleton_self a)
    intro p hp
    rw [List.foldlM_append, run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨x, c'⟩, hx, hp⟩ := hp
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure] at hp
    obtain ⟨hsub, heq, hzero⟩ := ih hl ⟨x, c'⟩ hx
    obtain ⟨hsub', hne, ha⟩ := G.reconStep_support A given x a c' p hp
    refine ⟨hsub.trans hsub', fun v hv => ?_, fun v hv => ?_⟩
    · rw [List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · have hva := hla' v hv
        exact ReconEqAt.congr G (fun u hu => hne u (ne_of_lt (lt_of_le_of_lt hu hva)))
          (ReconEqAt.mono G hsub' (heq v hv))
      · exact ha
    · rw [List.mem_append, List.mem_singleton, not_or] at hv
      rw [hne v hv.2]
      exact hzero v hv.1

/-- Every outcome of reconstruction satisfies the reconstruction equations with respect to the
final cache, which extends the initial one. -/
theorem reconstruct_support (A : Finset (Fin G.size)) (given : G.Assignment) (c : Cache) :
    ∀ p ∈ support (run (G.reconstruct A given) c),
      Cache.Sub c p.2 ∧ G.ReconEqs p.2 A given p.1 := by
  intro p hp
  rw [reconstruct_eq_foldlM] at hp
  obtain ⟨hsub, heq, -⟩ :=
    G.foldlM_reconStep_support A given c _ (List.pairwise_lt_finRange _) p hp
  exact ⟨hsub, fun v => heq v (List.mem_finRange v)⟩

/-! ## Encoding and decoding -/

/-- The members of `A` in node order. -/
theorem encode_eq (A : Finset (Fin G.size)) (x : G.Assignment) :
    G.encode A x =
      ((List.finRange G.size).filter fun v => decide (v ∈ A)).flatMap fun v => toBits (x v) := rfl

theorem revealBits_eq (A : Finset (Fin G.size)) :
    G.revealBits A = (((List.finRange G.size).filter fun v => decide (v ∈ A)).map G.len).sum := by
  unfold revealBits
  rw [← List.sum_toFinset _ ((List.nodup_finRange _).filter _)]
  congr 1
  ext v
  simp

theorem offset_eq (A : Finset (Fin G.size)) (v : Fin G.size) :
    G.offset A v = chunkOff G.len ((List.finRange G.size).filter fun v => decide (v ∈ A)) v := by
  unfold offset chunkOff
  rw [← List.sum_toFinset _ (((List.nodup_finRange _).filter _).filter _)]
  congr 1
  ext w
  simp [and_comm]

theorem length_encode (A : Finset (Fin G.size)) (x : G.Assignment) :
    (G.encode A x).length = G.revealBits A := by
  rw [encode_eq, revealBits_eq, List.length_flatMap]
  simp only [length_toBits]

theorem decode_encode (A : Finset (Fin G.size)) (x : G.Assignment) {v : Fin G.size}
    (hv : v ∈ A) : G.decode A (G.encode A x) v = x v := by
  unfold decode
  rw [encode_eq, offset_eq]
  set L := (List.finRange G.size).filter fun v => decide (v ∈ A) with hLdef
  have hL : L.Pairwise (· < ·) := (List.pairwise_lt_finRange _).filter _
  have hvL : v ∈ L := by simp [hLdef, hv]
  have hsplit : ∀ (M : List (Fin G.size)), M.Pairwise (· < ·) → v ∈ M →
      M.flatMap (fun w => toBits (x w)) =
        (M.filter fun w => decide (w < v)).flatMap (fun w => toBits (x w)) ++
          (toBits (x v) ++ (M.filter fun w => decide (v < w)).flatMap (fun w => toBits (x w))) := by
    intro M
    induction M with
    | nil => intro _ h; simp at h
    | cons a M ih =>
      intro hM hvM
      rw [List.pairwise_cons] at hM
      rcases List.mem_cons.1 hvM with rfl | hvM
      · have h1 : (M.filter fun w => decide (w < v)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro w hw
          simpa using le_of_lt (hM.1 w hw)
        have h2 : (M.filter fun w => decide (v < w)) = M := by
          rw [List.filter_eq_self]
          intro w hw
          simpa using hM.1 w hw
        simp [h1, h2]
      · have hav : a < v := hM.1 v hvM
        rw [List.flatMap_cons, ih hM.2 hvM]
        simp [hav, not_lt.2 hav.le]
  rw [hsplit L hL hvL]
  have hoff : chunkOff G.len L v =
      ((L.filter fun w => decide (w < v)).flatMap (fun w => toBits (x w))).length := by
    rw [List.length_flatMap]
    simp only [length_toBits]
    rfl
  rw [hoff, List.drop_left, List.take_left' (length_toBits _), ofBits_toBits]

theorem encode_decode (A : Finset (Fin G.size)) (l : List Bool)
    (hl : l.length = G.revealBits A) : G.encode A (G.decode A l) = l := by
  rw [encode_eq]
  unfold decode
  simp only [offset_eq]
  rw [revealBits_eq] at hl
  set L := (List.finRange G.size).filter fun v => decide (v ∈ A) with hLdef
  have hL : L.Pairwise (· < ·) := (List.pairwise_lt_finRange _).filter _
  conv_rhs => rw [← flatMap_chunks G.len L hL l hl]
  refine flatMap_congr_mem fun v hv => ?_
  apply toBits_ofBits
  rw [List.length_take, List.length_drop, hl]
  have := chunkOff_add_le G.len L hL v hv
  omega

end Dag.Graph

/-- The index query records its answer in the cache. -/
theorem index_support (m : Message) (η : Nonce) (c : Cache) :
    ∀ p ∈ support (run (index m η) c),
      Cache.Sub c p.2 ∧ ∃ w, p.2 ⟨msgBits + nonceBits, m ++ η⟩ = some w ∧
        p.1 = (w.setWidth idxBits).toNat := by
  intro p hp
  unfold index at hp
  rw [run_map, support_map, Set.mem_image] at hp
  obtain ⟨⟨w, c'⟩, hw, rfl⟩ := hp
  obtain ⟨hsub, hc'⟩ := hash_support _ c _ hw
  dsimp only at hsub hc' ⊢
  exact ⟨hsub, w, hc', rfl⟩

/-- Every accepting run of the verifier is witnessed in the final cache: the index answer, and
an assignment satisfying the reconstruction equations whose root prefix is the public key. -/
theorem verify_support (S : GScheme) (pk : PublicKey) (m : Message)
    (σ : Signature) (c : Cache) :
    ∀ p ∈ support (run (S.verify pk m σ) c),
      Cache.Sub c p.2 ∧ (p.1 = true →
        ∃ w, p.2 ⟨msgBits + nonceBits, m ++ σ.1⟩ = some w ∧
          ∃ hi : (w.setWidth idxBits).toNat ∈ validSet,
            σ.2.length = S.graph.revealBits (S.sets ⟨_, hi⟩) ∧
            ∃ y : S.graph.Assignment,
              S.graph.ReconEqs p.2 (S.sets ⟨_, hi⟩) (S.graph.decode (S.sets ⟨_, hi⟩) σ.2) y ∧
              S.publicKey y = pk) := by
  intro p hp
  unfold GScheme.verify at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨i, c₁⟩, hi₁, hp⟩ := hp
  obtain ⟨hsub₁, w, hw, rfl⟩ := index_support m σ.1 c ⟨i, c₁⟩ hi₁
  dsimp only at hp hw
  by_cases hi : (w.setWidth idxBits).toNat ∈ validSet
  · rw [dif_pos hi] at hp
    by_cases hlen : σ.2.length = S.graph.revealBits (S.sets ⟨_, hi⟩)
    · rw [if_pos hlen, run_bind, support_bind] at hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨⟨y, c₂⟩, hy, hp⟩ := hp
      obtain ⟨hsub₂, heq⟩ := S.graph.reconstruct_support _ _ c₁ ⟨y, c₂⟩ hy
      rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      refine ⟨hsub₁.trans hsub₂, fun hok => ?_⟩
      refine ⟨w, hsub₂ _ _ hw, hi, hlen, y, heq, ?_⟩
      exact of_decide_eq_true hok
    · rw [if_neg hlen, run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hsub₁, fun h => by cases h⟩
  · rw [dif_neg hi, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hsub₁, fun h => by cases h⟩

end OptimalOTS
