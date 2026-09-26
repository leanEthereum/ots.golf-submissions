import Submissions.UpperLeanIsa.FusionCoherence

/-! Fixed-oracle semantics and perfect correctness of the dependency-aware scheme. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open OracleSpec OracleComp
open scoped Classical
noncomputable section

namespace Params
variable (P : Params)

def stepValue (f : HashTable) (t : Tops) (k : Fin 42) (j : ℕ) (x : Word) : Word :=
  P.codec.slice k j (f ⟨896,P.chainInput t k j x⟩)

def chainValue (f : HashTable) (t : Tops) (k : Fin 42) : ℕ → ℕ → Word → Word
  | _,0,x => x
  | j,n+1,x => chainValue f t k (j+1) n (P.stepValue f t k j x)

def reconFromValue (f : HashTable) (I : Index) (bits : List Bool) : List (Fin 42) → Tops → Tops
  | [],t => t
  | k::l,t => reconFromValue f I bits l (Function.update t k.val
      (P.chainValue f t k (P.codec.len k - 1 - P.codec.digit I k)
        (P.codec.digit I k) (decodeWord bits k)))

def rootFromValue (f : HashTable) (t : Tops) : List (Fin 3) → BitVec 256 → BitVec 256
  | [],st => st
  | r::l,st => rootFromValue f t l (f ⟨896,P.rootInput t r st⟩)

def rootValue (f : HashTable) (t : Tops) : PublicKey :=
  (P.rootFromValue f t [0,1,2] 0).extractLsb' 0 128

def verifyValue (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) : Bool :=
  if bits.length ≠ sigBits then false
  else if ¬ P.codec.Accepted (P.codec.idxValue f m (decodeNonce bits) pk) then false
  else P.rootValue f (P.reconFromValue f (P.codec.idxValue f m (decodeNonce bits) pk)
    bits chainOrder (fun _ => 0)) == pk

def keygenRecord (f : HashTable) (seeds : Fin 42 → Word) : Record P :=
  (seeds,P.evalLocationsValue f seeds P.locationOrder (fun _ => 0))

def keygenValue (f : HashTable) (seeds : Fin 42 → Word) : PublicKey × SecretKey :=
  let ξ := P.keygenRecord f seeds
  (ξ.pk,ξ.sk)

theorem fixed_chain (f : HashTable) (t : Tops) (k : Fin 42) (j n : ℕ) (x : Word) :
    simulateQ (unifFwdAnswerImpl f) (P.chain t k j n x) = pure (P.chainValue f t k j n x) := by
  induction n generalizing j x with
  | zero => rfl
  | succ n ih =>
    simp only [chain,chainStep,simulateQ_bind,simulateQ_map,Layer.Params.fixed_hash,
      map_pure,pure_bind,ih]
    rfl

theorem fixed_reconFrom (f : HashTable) (I : Index) (bits : List Bool)
    (l : List (Fin 42)) (t : Tops) :
    simulateQ (unifFwdAnswerImpl f) (P.reconFrom I bits l t) =
      pure (P.reconFromValue f I bits l t) := by
  induction l generalizing t with
  | nil => rfl
  | cons k l ih =>
    simp only [reconFrom,simulateQ_bind,fixed_chain,pure_bind,ih]
    rfl

theorem fixed_rootFrom (f : HashTable) (t : Tops) (l : List (Fin 3)) (st : BitVec 256) :
    simulateQ (unifFwdAnswerImpl f) (P.rootFrom t l st) = pure (P.rootFromValue f t l st) := by
  induction l generalizing st with
  | nil => rfl
  | cons r l ih =>
    rw [rootFrom,simulateQ_bind,Layer.Params.fixed_hash,pure_bind]
    exact ih _

theorem fixed_root (f : HashTable) (t : Tops) :
    simulateQ (unifFwdAnswerImpl f) (P.root t) = pure (P.rootValue f t) := by
  simp only [root,simulateQ_map,fixed_rootFrom,map_pure]
  rfl

theorem fixed_verify (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) :
    simulateQ (unifFwdAnswerImpl f) (P.verify pk m bits) = pure (P.verifyValue f pk m bits) := by
  by_cases hl : bits.length = sigBits
  · simp only [verify,hl,ne_eq,not_true_eq_false,if_false,simulateQ_bind,
      Layer.Params.fixed_index,pure_bind]
    by_cases ha : P.codec.Accepted (P.codec.idxValue f m (decodeNonce bits) pk)
    · simp only [ha,not_true_eq_false,if_false,simulateQ_bind,fixed_reconFrom,pure_bind,
        fixed_root,simulateQ_pure,verifyValue,hl,ne_eq]
    · simp only [ha,not_false_eq_true,if_true,simulateQ_pure,verifyValue,hl,ne_eq,
        not_true_eq_false,if_false]
  · simp only [verify,hl,ne_eq,not_false_eq_true,if_true,simulateQ_pure,verifyValue]

theorem fixed_keygen (f : HashTable) :
    simulateQ (unifFwdAnswerImpl f) P.keygen =
      (simulateQ (unifFwdAnswerImpl f) (tabulate (fun _ : Fin 42 => sampleBits 128)) >>=
        fun seeds => pure (P.keygenValue f seeds)) := by
  simp only [keygen,simulateQ_bind,simulateQ_pure,fixed_evalLocations,pure_bind]
  rfl

theorem chainValue_add (f : HashTable) (t : Tops) (k : Fin 42) (j a b : ℕ) (x : Word) :
    P.chainValue f t k (j+a) b (P.chainValue f t k j a x) = P.chainValue f t k j (a+b) x := by
  induction a generalizing j x with
  | zero => simp only [chainValue,Nat.add_zero,Nat.zero_add]
  | succ a ih =>
    simp only [Nat.succ_add,chainValue]
    simpa only [Nat.add_assoc,Nat.add_comm 1 a] using ih (j+1) (P.stepValue f t k j x)

theorem chainValue_snoc (f : HashTable) (t : Tops) (k : Fin 42) (j n : ℕ) (x : Word) :
    P.chainValue f t k j (n+1) x = P.stepValue f t k (j+n) (P.chainValue f t k j n x) := by
  rw [← P.chainValue_add f t k j n 1 x]
  rfl

def Coherent (f : HashTable) (ξ : Record P) : Prop := ∀ a, ξ.2 a = f (ξ.query a)

theorem keygenRecord_coherent (hl : P.locationOrder.Pairwise Earlier)
    (f : HashTable) (seeds : Fin 42 → Word) : P.Coherent f (P.keygenRecord f seeds) := by
  intro a
  exact P.evalLocationsValue_coherent f seeds _ hl _ a (P.locationOrder_mem a)

theorem chainValue_coherent (f : HashTable) (ξ : Record P) (hc : P.Coherent f ξ)
    (t : Tops) (k : Fin 42)
    (ht : ∀ u : Fin 6, owner k = some u → ∀ d ∈ children u, t d = ξ.tops d)
    (j n : ℕ) (hn : j+n < P.codec.len k) :
    P.chainValue f t k j n (ξ.word k j) = ξ.word k (j+n) := by
  induction n generalizing j with
  | zero => simp only [chainValue,Nat.add_zero]
  | succ n ih =>
    have hj : j < P.codec.len k - 1 := by omega
    have hs : P.stepValue f t k j (ξ.word k j) = ξ.word k (j+1) := by
      rw [stepValue,Params.chainInput_congr t ξ.tops k j _ ht,Record.word_succ ξ k j hj]
      exact congrArg (P.codec.slice k j) (hc (.inl ⟨k,⟨j,hj⟩⟩)).symm
    rw [chainValue,hs,ih (j+1) (by omega)]
    congr 1
    omega

theorem table_getD (ξ : Record P) (k : Fin 42) (j : ℕ) (hj : j < P.codec.len k) :
    (ξ.table k).getD j 0 = ξ.word k j := by
  simp [Record.table,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,hj]

theorem reconFromValue_honest (hP : P.codec.Hyp) (f : HashTable) (ξ : Record P)
    (hc : P.Coherent f ξ) (I : Index) (η : Nonce) (l : List (Fin 42))
    (hl : l.Pairwise (fun k k' => evaluationRank k.val < evaluationRank k'.val))
    (t : Tops) (ht : ∀ d, d ∉ l.map Fin.val → t d = ξ.tops d) :
    P.reconFromValue f I (encode (P.codec.revealed ξ.sk I) η) l t = ξ.tops := by
  induction l generalizing t with
  | nil => exact funext fun d => ht d (by simp)
  | cons k l ih =>
    obtain ⟨hbefore,hl⟩ := List.pairwise_cons.mp hl
    have hdep : ∀ u : Fin 6, owner k = some u → ∀ d ∈ children u, t d = ξ.tops d := by
      intro u hu d hd
      apply ht d
      intro hmem
      have hr := dependency_precedes u u.isLt k.val ((owner_mem k u).mp hu) d hd
      obtain ⟨k',hk',he⟩ := List.mem_map.mp hmem
      rcases List.mem_cons.mp hk' with he' | hk'
      · have heq : d = k.val := he.symm.trans (congrArg Fin.val he')
        rw [heq] at hr
        omega
      · have hh := hbefore k' hk'
        rw [he] at hh
        omega
    have hd := hP.digit_lt I k
    have hreveal : decodeWord (encode (P.codec.revealed ξ.sk I) η) k =
        ξ.word k (P.codec.len k - 1 - P.codec.digit I k) := by
      rw [decodeWord_encode]
      exact P.table_getD ξ k _ (by omega)
    have hchain : P.chainValue f t k (P.codec.len k - 1 - P.codec.digit I k)
        (P.codec.digit I k) (decodeWord (encode (P.codec.revealed ξ.sk I) η) k) = ξ.top k := by
      rw [hreveal,P.chainValue_coherent f ξ hc t k hdep _ _ (by omega)]
      unfold Record.top
      congr 1
      omega
    rw [reconFromValue,hchain]
    apply ih hl
    intro d hd'
    by_cases he : d = k.val
    · subst d
      rw [Function.update_self]
      simp only [Record.tops,Layer.Params.topAt,dif_pos k.isLt]
    · rw [Function.update_of_ne he]
      exact ht d (by simpa only [List.map_cons,List.mem_cons,not_or] using ⟨he,hd'⟩)

theorem rootValue_coherent (f : HashTable) (ξ : Record P) (hc : P.Coherent f ξ) :
    P.rootValue f ξ.tops = ξ.pk := by
  have h0 : f ⟨896,P.rootInput ξ.tops 0 0⟩ = ξ.2 (.inr 0) := (hc (.inr 0)).symm
  have h1 : f ⟨896,P.rootInput ξ.tops 1 (ξ.2 (.inr 0))⟩ = ξ.2 (.inr 1) := (hc (.inr 1)).symm
  have h2 : f ⟨896,P.rootInput ξ.tops 2 (ξ.2 (.inr 1))⟩ = ξ.2 (.inr 2) := (hc (.inr 2)).symm
  dsimp only [rootValue,rootFromValue]
  rw [h0,h1,h2]
  rfl

theorem chainOrder_ranked : chainOrder.Pairwise
    (fun k k' => evaluationRank k.val < evaluationRank k'.val) := by decide

theorem verifyValue_honest (hP : P.codec.Hyp) (hl : P.locationOrder.Pairwise Earlier)
    (f : HashTable) (seeds : Fin 42 → Word) (m : Message) (η : Nonce)
    (ha : P.codec.Accepted (P.codec.idxValue f m η (P.keygenValue f seeds).2.pk)) :
    P.verifyValue f (P.keygenValue f seeds).1 m
      (encode (P.codec.revealed (P.keygenValue f seeds).2
        (P.codec.idxValue f m η (P.keygenValue f seeds).2.pk)) η) = true := by
  let ξ := P.keygenRecord f seeds
  change P.codec.Accepted (P.codec.idxValue f m η ξ.pk) at ha
  change P.verifyValue f ξ.pk m (encode (P.codec.revealed ξ.sk
    (P.codec.idxValue f m η ξ.pk)) η) = true
  rw [verifyValue,encode_length,decodeNonce_encode]
  simp only [ne_eq,not_true_eq_false,if_false,ha]
  have hc := P.keygenRecord_coherent hl f seeds
  rw [P.reconFromValue_honest hP f ξ hc _ η chainOrder chainOrder_ranked (fun _ => 0) ?_,
    P.rootValue_coherent f ξ hc]
  · simp
  · intro d hd
    have hge : ¬ d < 42 := by
      intro hlt
      exact hd (List.mem_map.mpr ⟨⟨d,hlt⟩,chainOrder_permutation.mem_iff.mpr
        (List.mem_finRange ⟨d,hlt⟩),rfl⟩)
    simp only [Record.tops,Layer.Params.topAt,dif_neg hge]

theorem correct (hP : P.codec.Hyp) (hl : P.locationOrder.Pairwise Earlier) : P.scheme.Correct := by
  intro message
  apply Layer.Params.probTrue_zero_of_fixed
  intro f hmem
  dsimp only [Params.scheme] at hmem
  rw [simulateQ_bind,support_bind] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨⟨pk,sk⟩,hk,hmem⟩ := hmem
  have hk' : (pk,sk) ∈ support (simulateQ (unifFwdAnswerImpl f) P.keygen) := hk
  rw [fixed_keygen,support_bind] at hk'
  rw [Set.mem_iUnion₂] at hk'
  obtain ⟨seeds,-,hkv⟩ := hk'
  rw [support_pure,Set.mem_singleton_iff] at hkv
  dsimp only at hmem
  rw [simulateQ_bind,support_bind] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨σ,hσ,hmem⟩ := hmem
  rcases σ with _ | s
  · simp only [simulateQ_pure,support_pure,Set.mem_singleton_iff] at hmem
    cases hmem
  · have hσ' : some s ∈ support (simulateQ (unifFwdAnswerImpl f) (P.codec.sign sk (message pk))) := hσ
    obtain ⟨η,ha,rfl⟩ := P.codec.fixed_sign_support f _ _ s hσ'
    dsimp only at hmem
    rw [simulateQ_bind,fixed_verify,pure_bind,simulateQ_pure,support_pure,Set.mem_singleton_iff] at hmem
    have hpk : pk = (P.keygenValue f seeds).1 := congrArg Prod.fst hkv
    have hsk : sk = (P.keygenValue f seeds).2 := congrArg Prod.snd hkv
    subst hpk hsk
    rw [P.verifyValue_honest hP hl f seeds _ η ha] at hmem
    cases hmem

end Params

theorem concrete_correct : params.scheme.Correct :=
  params.correct params_hyp.codec concrete_ordered

end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
