import Submissions.LowerGenerality1.Encoding
import Submissions.LowerGenerality1.Cache
import Submissions.LowerGenerality1.KeygenSupport

/-!
# Moving disclosed values between equal reconstruction patterns

Candidates are algebraic records satisfying observed node equations. No probability law on
records is assumed. If a target reconstructs only hash nodes already reconstructed at the signed
index, every candidate supplies an accepted target disclosure under the same oracle.
-/

open OracleSpec OracleComp ENNReal

noncomputable section
open scoped Classical
namespace OptimalOTS.Conversion

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (S : Scheme)

abbrev evalHashAt (i : Fin numCuts) := S.graph.evalHash (S.sets i)

def cands (i : Fin numCuts) (xa xr : S.graph.Assignment) : Finset S.graph.Rec :=
  Finset.univ.filter fun ξ =>
    (∀ v ∈ S.sets i, S.graph.evalRec ξ v = xa v) ∧
      ∀ g ∈ evalHashAt S i, ξ.2 g = (S.graph.kind g).output (xr g)

def obsCands (i : Fin numCuts) (ξ : S.graph.Rec) : Finset S.graph.Rec :=
  Finset.univ.filter fun ξ' =>
    (∀ v ∈ S.sets i, S.graph.evalRec ξ' v = S.graph.evalRec ξ v) ∧
      ∀ g ∈ evalHashAt S i, ξ'.2 g = ξ.2 g

open Encoding

theorem value_ne_source {v : Fin S.graph.size} (x : S.graph.Assignment)
    (s s' : BitVec (S.graph.len v)) (a : BitVec hashBits) (h : ¬ (S.graph.kind v).IsSource) :
    (S.graph.kind v).value x s a = (S.graph.kind v).value x s' a := by
  revert h
  generalize S.graph.kind v = k
  cases k <;> intro h
  · exact absurd trivial h
  · rfl
  · rfl

theorem value_nonHash {v : Fin S.graph.size} (x : S.graph.Assignment)
    (s : BitVec (S.graph.len v)) (a a' : BitVec hashBits) (h : ¬ (S.graph.kind v).IsHash) :
    (S.graph.kind v).value x s a = (S.graph.kind v).value x s a' := by
  revert h
  generalize S.graph.kind v = k
  cases k <;> intro h
  · rfl
  · rfl
  · exact absurd trivial h

theorem output_value_hash {v : Fin S.graph.size} (x : S.graph.Assignment)
    (s : BitVec (S.graph.len v)) (a : BitVec hashBits) (h : (S.graph.kind v).IsHash) :
    (S.graph.kind v).output ((S.graph.kind v).value x s a) = a := by
  revert h
  generalize S.graph.kind v = k
  cases k <;> intro h
  · exact absurd h id
  · exact absurd h id
  · simp [NodeKind.output, NodeKind.value]

theorem input_congr {v : Fin S.graph.size} (x y : S.graph.Assignment)
    (h : ∀ w ∈ (S.graph.kind v).parents, x w = y w) :
    (S.graph.kind v).input x = (S.graph.kind v).input y := by
  revert h
  generalize S.graph.kind v = k
  cases k <;> intro h
  · rfl
  · rfl
  · exact h _ (by simp [NodeKind.parents])

theorem evalTab_apply (z : S.graph.Assignment) (t : S.graph.Tab) (v : Fin S.graph.size) :
    S.graph.evalTab z t v = (S.graph.kind v).value (S.graph.evalTab z t) (z v)
      (t v ((S.graph.kind v).input (S.graph.evalTab z t))) :=
  S.graph.evalWith_apply (S.graph.parentLocal_tabVal z t) v

theorem mem_evalHashAt (i : Fin numCuts) (v : Fin S.graph.size) :
    v ∈ evalHashAt S i ↔
      S.graph.Visited (S.sets i) v ∧ v ∉ S.sets i ∧ (S.graph.kind v).IsHash := by
  simp [evalHashAt, Graph.evalHash, Graph.evaluated, and_assoc]

theorem reconTab_congr (tg : S.graph.Tab) (A : Finset (Fin S.graph.size))
    (given given' : S.graph.Assignment) (h : ∀ v ∈ A, given v = given' v) :
    S.graph.reconTab tg A given = S.graph.reconTab tg A given' := by
  unfold Graph.reconTab
  congr 1
  funext v x
  simp only [Graph.reconVal]
  split_ifs with hv
  · exact h v hv
  · rfl
  · rfl

theorem reconTab_decode_encode_eq (tg : S.graph.Tab) (i : Fin numCuts) (a : S.graph.Assignment)
    (ha : ∀ v, S.graph.Visited (S.sets i) v → v ∉ S.sets i →
      a v = (S.graph.kind v).value a 0 (tg v ((S.graph.kind v).input a)))
    (v : Fin S.graph.size) (hv : S.graph.Visited (S.sets i) v) :
    S.graph.reconTab tg (S.sets i) (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) a)) v =
      a v := by
  rw [reconTab_congr S tg _ _ a (fun w hw => decode_encode _ a w hw)]
  exact S.graph.reconTab_eq_of_visited tg _ a (S.no_hidden_source i) ha v hv

theorem evalTab_nodeEqs (z : S.graph.Assignment) (tg : S.graph.Tab) (i : Fin numCuts) :
    ∀ v, S.graph.Visited (S.sets i) v → v ∉ S.sets i →
      S.graph.evalTab z tg v = (S.graph.kind v).value (S.graph.evalTab z tg) 0
        (tg v ((S.graph.kind v).input (S.graph.evalTab z tg))) := by
  intro v hv hA
  conv_lhs => rw [evalTab_apply]
  exact value_ne_source S _ _ _ _ (S.no_hidden_source i v hv hA)

theorem mem_obsCands (i : Fin numCuts) (ξ ξ' : S.graph.Rec) :
    ξ' ∈ obsCands S i ξ ↔
      (∀ v ∈ S.sets i, S.graph.evalRec ξ' v = S.graph.evalRec ξ v) ∧
        ∀ k ∈ evalHashAt S i, ξ'.2 k = ξ.2 k := by
  simp only [obsCands, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_cands (i : Fin numCuts) (xa xr : S.graph.Assignment) (ξ' : S.graph.Rec) :
    ξ' ∈ cands S i xa xr ↔
      (∀ v ∈ S.sets i, S.graph.evalRec ξ' v = xa v) ∧
        ∀ g ∈ evalHashAt S i, ξ'.2 g = (S.graph.kind g).output (xr g) :=
  ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩

theorem cand_agree (i : Fin numCuts) (ξ ξ' : S.graph.Rec) (h : ξ' ∈ obsCands S i ξ) :
    ∀ v, S.graph.Visited (S.sets i) v → S.graph.evalRec ξ' v = S.graph.evalRec ξ v := by
  obtain ⟨hrev, hout⟩ := (mem_obsCands S i ξ ξ').1 h
  intro v
  induction v using WellFoundedLT.induction with
  | _ v ih =>
    intro hv
    by_cases hA : v ∈ S.sets i
    · exact hrev v hA
    · have hns := S.no_hidden_source i v hv hA
      rw [S.graph.evalRec_apply ξ', S.graph.evalRec_apply ξ,
        value_ne_source S _ (ξ'.1 v) (ξ.1 v) _ hns]
      have h2 : (S.graph.kind v).value (S.graph.evalRec ξ') (ξ.1 v) (ξ'.2 v) =
          (S.graph.kind v).value (S.graph.evalRec ξ') (ξ.1 v) (ξ.2 v) := by
        by_cases hh : (S.graph.kind v).IsHash
        · rw [hout v ((mem_evalHashAt S i v).2 ⟨hv, hA, hh⟩)]
        · exact value_nonHash S _ _ _ _ hh
      rw [h2]
      exact NodeKind.value_congr _ _ _ _ _ fun w hw =>
        ih w ((S.graph.kind v).lt_of_mem_parents hw) (Graph.Visited.parent hv hA hw)

theorem cands_eq (i : Fin numCuts) (z : S.graph.Assignment) (tg : S.graph.Tab) :
    cands S i (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) (S.graph.evalTab z tg)))
      (S.graph.reconTab tg (S.sets i)
        (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) (S.graph.evalTab z tg)))) =
    obsCands S i (S.graph.recOf z tg) := by
  have hxr := reconTab_decode_encode_eq S tg i _ (evalTab_nodeEqs S z tg i)
  ext ξ'
  rw [mem_cands, mem_obsCands]
  apply and_congr
  · constructor
    · intro h v hv
      rw [Graph.evalRec_recOf, h v hv, decode_encode _ _ v hv]
    · intro h v hv
      rw [h v hv, Graph.evalRec_recOf, decode_encode _ _ v hv]
  · apply forall₂_congr
    intro v hv
    have hv' := (mem_evalHashAt S i v).1 hv
    rw [hxr v hv'.1]
    conv_lhs => rw [evalTab_apply]
    rw [output_value_hash S _ _ _ hv'.2.2]
    rfl

theorem forged_nodeEqs (i j : Fin numCuts) (z : S.graph.Assignment) (tg : S.graph.Tab)
    (ξ' : S.graph.Rec) (hc : ξ' ∈ obsCands S i (S.graph.recOf z tg))
    (hsub : evalHashAt S j ⊆ evalHashAt S i) :
    ∀ v, S.graph.Visited (S.sets j) v → v ∉ S.sets j →
      S.graph.evalRec ξ' v = (S.graph.kind v).value (S.graph.evalRec ξ') 0
        (tg v ((S.graph.kind v).input (S.graph.evalRec ξ'))) := by
  intro v hv hA
  have hns := S.no_hidden_source j v hv hA
  conv_lhs => rw [S.graph.evalRec_apply ξ']
  rw [value_ne_source S _ (ξ'.1 v) 0 _ hns]
  by_cases hh : (S.graph.kind v).IsHash
  · congr 1
    by_cases hi : v ∈ evalHashAt S i
    · have hout := ((mem_obsCands S i _ ξ').1 hc).2 v hi
      rw [hout]
      have hi' := (mem_evalHashAt S i v).1 hi
      change tg v ((S.graph.kind v).input (S.graph.evalTab z tg)) = _
      rw [← Graph.evalRec_recOf]
      exact congrArg (tg v) (input_congr S _ _ fun w hw =>
        (cand_agree S i _ ξ' hc w (Graph.Visited.parent hi'.1 hi'.2.1 hw)).symm)
    · exact (hi (hsub ((mem_evalHashAt S j v).2 ⟨hv, hA, hh⟩))).elim
  · exact value_nonHash S _ _ _ _ hh

theorem forged_root (i : Fin numCuts) (z : S.graph.Assignment) (tg : S.graph.Tab)
    (ξ' : S.graph.Rec) (hc : ξ' ∈ obsCands S i (S.graph.recOf z tg)) :
    S.graph.evalRec ξ' S.graph.root = S.graph.evalTab z tg S.graph.root := by
  rw [cand_agree S i _ ξ' hc _ Graph.Visited.root, Graph.evalRec_recOf]


/-- Choose a candidate using only the observations; computational effort is uncharged. -/
def chooseRecord (i : Fin numCuts) (xa xr : S.graph.Assignment) : S.graph.Rec :=
  if h : (cands S i xa xr).Nonempty then Classical.choose h else
    (fun _ => 0, fun _ => 0)

theorem chooseRecord_mem (i : Fin numCuts) (xa xr : S.graph.Assignment)
    (h : (cands S i xa xr).Nonempty) :
    chooseRecord S i xa xr ∈ cands S i xa xr := by
  simp only [chooseRecord, dif_pos h]
  exact Classical.choose_spec h

def convert (i j : Fin numCuts) (xa xr : S.graph.Assignment) : List Bool :=
  S.graph.encode (S.sets j) (S.graph.evalRec (chooseRecord S i xa xr))

theorem length_convert (i j : Fin numCuts) (xa xr : S.graph.Assignment) :
    (convert S i j xa xr).length = S.graph.revealBits (S.sets j) :=
  length_encode _ _

/-- A candidate makes exactly the already known input query at every old evaluated hash. -/
theorem candidate_input_eq (i : Fin numCuts) (ξ ξ' : S.graph.Rec)
    (hc : ξ' ∈ obsCands S i ξ) (v : Fin S.graph.size) (hv : v ∈ evalHashAt S i) :
    (S.graph.kind v).input (S.graph.evalRec ξ') =
      (S.graph.kind v).input (S.graph.evalRec ξ) := by
  have hv' := (mem_evalHashAt S i v).1 hv
  exact input_congr S _ _ fun w hw =>
    cand_agree S i ξ ξ' hc w (Graph.Visited.parent hv'.1 hv'.2.1 hw)

/-- A total pure disclosure converter preserves the root when no new hash node is evaluated. -/
theorem recon_convert_root (i j : Fin numCuts) (z : S.graph.Assignment) (tg : S.graph.Tab)
    (hsub : evalHashAt S j ⊆ evalHashAt S i) :
    let xa := S.graph.decode (S.sets i) (S.graph.encode (S.sets i) (S.graph.evalTab z tg))
    let xr := S.graph.reconTab tg (S.sets i) xa
    S.graph.reconTab tg (S.sets j) (S.graph.decode (S.sets j) (convert S i j xa xr))
      S.graph.root = S.graph.evalTab z tg S.graph.root := by
  intro xa xr
  have heq : cands S i xa xr = obsCands S i (S.graph.recOf z tg) := cands_eq S i z tg
  have hn : (cands S i xa xr).Nonempty := by
    rw [heq]
    refine ⟨S.graph.recOf z tg, ?_⟩
    rw [mem_obsCands]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hc : chooseRecord S i xa xr ∈ obsCands S i (S.graph.recOf z tg) := by
    rw [← heq]
    exact chooseRecord_mem S i xa xr hn
  unfold convert
  rw [reconTab_decode_encode_eq S tg j _ (forged_nodeEqs S i j z tg _ hc hsub)
    _ Graph.Visited.root]
  exact forged_root S i z tg _ hc

/-- A cached hash evaluation is deterministic and preserves the cache. -/
theorem run_evalNode_cached (x : S.graph.Assignment) (v : Fin S.graph.size)
    (s : BitVec (S.graph.len v)) (a : BitVec hashBits) (c : Cache)
    (hc : (S.graph.kind v).IsHash →
      c ⟨(S.graph.kind v).inLen, (S.graph.kind v).input x⟩ = some a) :
    run (S.graph.evalNode x v (pure s)) c =
      pure ((S.graph.kind v).value x s a, c) := by
  unfold Graph.evalNode
  generalize hk : S.graph.kind v = k at hc ⊢
  cases k with
  | source => exact run_pure s c
  | det ps hps f hf => exact run_pure (f x) c
  | hash p hp hl =>
    have hh := hc trivial
    simp only [NodeKind.inLen, NodeKind.input] at hh
    rw [run_map]
    have hr : run (hash (x p)) c = pure (a, c) := by
      unfold hash run
      rw [simulateQ_spec_query, oracleImpl_run_inr_some hh]
    rw [hr]
    rfl

/-- Root reconstruction uses no fresh oracle entries if its table answers are cached. -/
theorem run_reconstruct_cached (tg : S.graph.Tab) (A : Finset (Fin S.graph.size))
    (given : S.graph.Assignment) (c : Cache)
    (hc : ∀ v ∈ S.graph.evalHash A,
      c ⟨(S.graph.kind v).inLen,
        (S.graph.kind v).input (S.graph.reconTab tg A given)⟩ =
        some (tg v ((S.graph.kind v).input (S.graph.reconTab tg A given)))) :
    run (S.graph.reconstruct A given) c = pure (S.graph.reconTab tg A given, c) := by
  let y := S.graph.reconTab tg A given
  let step : S.graph.Assignment → Fin S.graph.size → OracleComp Spec S.graph.Assignment :=
    fun x v =>
    if v ∈ A then pure (Function.update x v (given v))
    else if S.graph.Visited A v then
      Function.update x v <$> S.graph.evalNode x v (pure 0)
    else pure (Function.update x v 0)
  have hy : ∀ v, y v = S.graph.reconVal tg A given v y :=
    S.graph.evalWith_apply (S.graph.parentLocal_reconVal tg A given)
  have hstep : ∀ x v, (∀ w ∈ (S.graph.kind v).parents, x w = y w) →
      run (step x v) c = pure (Function.update x v (y v), c) := by
    intro x v hparents
    dsimp only [step]
    by_cases hA : v ∈ A
    · rw [if_pos hA, run_pure]
      rw [hy v]
      simp only [Graph.reconVal, hA, if_true]
    · rw [if_neg hA]
      by_cases hV : S.graph.Visited A v
      · rw [if_pos hV, run_map,
          run_evalNode_cached S x v 0 (tg v ((S.graph.kind v).input x)) c (fun hh => ?_)]
        · simp only [map_pure]
          congr 2
          rw [hy v]
          simp only [Graph.reconVal, hA, hV, if_false, if_true]
          exact congrArg (Function.update x v) (NodeKind.value_input_congr _ _ (tg v) x y hparents)
        · rw [input_congr S x y hparents]
          exact hc v (by simp [Graph.evalHash, Graph.evaluated, hV, hA, hh])
      · rw [if_neg hV, run_pure, hy v]
        simp only [Graph.reconVal, hA, hV, if_false]
  have hfold : ∀ (l : List (Fin S.graph.size)), l.Pairwise (· < ·) →
      ∀ (x : S.graph.Assignment), (∀ w, w ∉ l → x w = y w) →
        run (l.foldlM step x) c = pure (y,c) := by
    intro l hl
    induction l with
    | nil =>
      intro x hx
      have he : x = y := funext fun w => hx w (by simp)
      subst he
      exact run_pure y c
    | cons a l ih =>
      rw [List.pairwise_cons] at hl
      intro x hx
      have hpar : ∀ w ∈ (S.graph.kind a).parents, x w = y w := by
        intro w hw
        apply hx
        intro hm
        have hwa := (S.graph.kind a).lt_of_mem_parents hw
        rcases List.mem_cons.1 hm with rfl | hm
        · exact (lt_irrefl _ hwa)
        · exact (not_lt_of_ge (hl.1 w hm).le hwa)
      rw [List.foldlM_cons, run_bind, hstep x a hpar, pure_bind]
      apply ih hl.2
      intro w hw
      dsimp only
      by_cases he : w = a
      · subst he; exact Function.update_self ..
      · rw [Function.update_of_ne he]
        exact hx w (by simp [he, hw])
  exact hfold (List.finRange S.graph.size) (List.pairwise_lt_finRange _) _
    (fun w hw => (hw (List.mem_finRange w)).elim)

/-- The cached-reconstruction theorem with hypotheses on a proposed complete assignment. -/
theorem run_reconstruct_encode_cached (tg : S.graph.Tab) (j : Fin numCuts)
    (a : S.graph.Assignment) (c : Cache)
    (ha : ∀ v, S.graph.Visited (S.sets j) v → v ∉ S.sets j →
      a v = (S.graph.kind v).value a 0 (tg v ((S.graph.kind v).input a)))
    (hc : ∀ v ∈ evalHashAt S j,
      c ⟨(S.graph.kind v).inLen, (S.graph.kind v).input a⟩ =
        some (tg v ((S.graph.kind v).input a))) :
    run (S.graph.reconstruct (S.sets j)
      (S.graph.decode (S.sets j) (S.graph.encode (S.sets j) a))) c =
      pure (S.graph.reconTab tg (S.sets j)
        (S.graph.decode (S.sets j) (S.graph.encode (S.sets j) a)), c) := by
  apply run_reconstruct_cached S
  intro v hv
  have hv' := (mem_evalHashAt S j v).1 hv
  have he : (S.graph.kind v).input (S.graph.reconTab tg (S.sets j)
      (S.graph.decode (S.sets j) (S.graph.encode (S.sets j) a))) =
      (S.graph.kind v).input a := by
    apply input_congr S
    intro w hw
    exact reconTab_decode_encode_eq S tg j a ha w (Graph.Visited.parent hv'.1 hv'.2.1 hw)
  rw [he]
  exact hc v hv

/-- Conversion runs entirely on cache entries already present after the honest reconstruction. -/
theorem run_convert_reconstruct (i j : Fin numCuts) (z : S.graph.Assignment)
    (tg : S.graph.Tab) (c : Cache) (hsub : evalHashAt S j ⊆ evalHashAt S i)
    (hcache : ∀ v ∈ evalHashAt S i,
      c ⟨(S.graph.kind v).inLen, (S.graph.kind v).input (S.graph.evalTab z tg)⟩ =
        some (tg v ((S.graph.kind v).input (S.graph.evalTab z tg)))) :
    let xa := S.graph.decode (S.sets i) (S.graph.encode (S.sets i) (S.graph.evalTab z tg))
    let xr := S.graph.reconTab tg (S.sets i) xa
    run (S.graph.reconstruct (S.sets j) (S.graph.decode (S.sets j) (convert S i j xa xr))) c =
      pure (S.graph.reconTab tg (S.sets j) (S.graph.decode (S.sets j) (convert S i j xa xr)), c) := by
  intro xa xr
  have heq : cands S i xa xr = obsCands S i (S.graph.recOf z tg) := cands_eq S i z tg
  have hn : (cands S i xa xr).Nonempty := by
    rw [heq]
    refine ⟨S.graph.recOf z tg, ?_⟩
    rw [mem_obsCands]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hξ : chooseRecord S i xa xr ∈ obsCands S i (S.graph.recOf z tg) := by
    rw [← heq]
    exact chooseRecord_mem S i xa xr hn
  apply run_reconstruct_encode_cached S tg j _ c (forged_nodeEqs S i j z tg _ hξ hsub)
  intro v hv
  have he := candidate_input_eq S i _ _ hξ v (hsub hv)
  rw [Graph.evalRec_recOf] at he
  rw [he]
  exact hcache v (hsub hv)

/-- A cached index query preserves the cache. -/
theorem run_index_cached (m : Message) (η : Nonce) (c : Cache)
    (w : BitVec hashBits) (hc : c ⟨msgBits + nonceBits, m ++ η⟩ = some w) :
    run (index m η) c = pure ((w.setWidth idxBits).toNat, c) := by
  unfold index
  rw [run_map]
  have hh : run (hash (m ++ η)) c = pure (w,c) := by
    unfold hash run
    rw [simulateQ_spec_query, oracleImpl_run_inr_some hc]
  rw [hh]
  rfl

/-- With a cached target index, the converted signature verifies deterministically. -/
theorem run_verify_convert (i j : Fin numCuts) (z : S.graph.Assignment)
    (tg : S.graph.Tab) (m : Message) (η : Nonce) (c : Cache)
    (hsub : evalHashAt S j ⊆ evalHashAt S i)
    (hcache : ∀ v ∈ evalHashAt S i,
      c ⟨(S.graph.kind v).inLen, (S.graph.kind v).input (S.graph.evalTab z tg)⟩ =
        some (tg v ((S.graph.kind v).input (S.graph.evalTab z tg))))
    (w : BitVec hashBits) (hw : c ⟨msgBits + nonceBits, m ++ η⟩ = some w)
    (hidx : (w.setWidth idxBits).toNat = j.val) :
    let xa := S.graph.decode (S.sets i) (S.graph.encode (S.sets i) (S.graph.evalTab z tg))
    let xr := S.graph.reconTab tg (S.sets i) xa
    run (S.verify (S.publicKey (S.graph.evalTab z tg)) m (η, convert S i j xa xr)) c =
      pure (true,c) := by
  intro xa xr
  unfold Scheme.verify
  rw [run_bind, run_index_cached m η c w hw, pure_bind]
  simp only
  generalize (w.setWidth idxBits).toNat = n at hidx ⊢
  subst hidx
  rw [dif_pos j.isLt]
  simp only [Fin.eta, length_convert, if_true]
  rw [run_bind, run_convert_reconstruct S i j z tg c hsub hcache, pure_bind, run_pure]
  congr 1
  apply Prod.ext
  · simp only [Scheme.publicKey, recon_convert_root S i j z tg hsub, decide_true]
  · rfl

/-- Complete a cache by zero at unseen strings, then use the resulting bare table at every node. -/
def cacheTab (c : Cache) : S.graph.Tab :=
  fun v u => (c ⟨(S.graph.kind v).inLen, u⟩).getD 0

theorem evalTab_cacheTab (x : S.graph.Assignment) (c : Cache)
    (hc : S.graph.CacheConsistent x c) : S.graph.evalTab x (cacheTab S c) = x := by
  symm
  apply S.graph.eq_evalWith (S.graph.parentLocal_tabVal x (cacheTab S c))
  intro v
  have hv := hc v
  unfold Graph.tabVal cacheTab
  cases hk : S.graph.kind v with
  | source => simp [hk, NodeKind.value]
  | det ps hps f hf =>
    simpa only [Graph.CacheEqAt, hk, NodeKind.value] using hv
  | hash p hp hl =>
    simp only [Graph.CacheEqAt, hk] at hv
    simp only [cacheTab, hk, NodeKind.input, NodeKind.inLen, NodeKind.value, hv,
      Option.getD_some, BitVec.cast_cast, BitVec.cast_eq]

theorem cacheTab_cached (x : S.graph.Assignment) (c : Cache)
    (hc : S.graph.CacheConsistent x c) (v : Fin S.graph.size)
    (hh : (S.graph.kind v).IsHash) :
    c ⟨(S.graph.kind v).inLen, (S.graph.kind v).input x⟩ =
      some (cacheTab S c v ((S.graph.kind v).input x)) := by
  have hv := hc v
  unfold cacheTab
  cases hk : S.graph.kind v with
  | source => simp [hk, NodeKind.IsHash] at hh
  | det ps hps f hf => simp [hk, NodeKind.IsHash] at hh
  | hash p hp hl =>
    simp only [Graph.CacheEqAt, hk] at hv
    simp only [cacheTab, hk, NodeKind.input, NodeKind.inLen, hv, Option.getD_some]

/-- Honest reconstruction has this assignment independently of the rest of the oracle. -/
def observed (i : Fin numCuts) (x : S.graph.Assignment) : S.graph.Assignment :=
  fun v => if v ∈ S.sets i ∨ S.graph.Visited (S.sets i) v then x v else 0

theorem recon_honest_eq_observed (i : Fin numCuts) (x : S.graph.Assignment) (c : Cache)
    (hc : S.graph.CacheConsistent x c) :
    S.graph.reconTab (cacheTab S c) (S.sets i)
      (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) x)) = observed S i x := by
  have hx := evalTab_cacheTab S x c hc
  have hnode := evalTab_nodeEqs S x (cacheTab S c) i
  rw [hx] at hnode
  funext v
  by_cases hv : S.graph.Visited (S.sets i) v
  · rw [reconTab_decode_encode_eq S _ i x hnode v hv]
    simp [observed, hv]
  · rw [Graph.reconTab, S.graph.evalWith_apply (S.graph.parentLocal_reconVal _ _ _)]
    by_cases hA : v ∈ S.sets i
    · simp only [Graph.reconVal, hA, if_true, decode_encode _ _ v hA]
      simp [observed, hA]
    · simp [Graph.reconVal, hA, hv, observed]

/-- The honest signed disclosure reconstructs deterministically using the key-generation cache. -/
theorem run_honest_reconstruct (i : Fin numCuts) (x : S.graph.Assignment) (c : Cache)
    (hc : S.graph.CacheConsistent x c) :
    run (S.graph.reconstruct (S.sets i)
      (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) x))) c =
      pure (observed S i x, c) := by
  have hx := evalTab_cacheTab S x c hc
  have hnode := evalTab_nodeEqs S x (cacheTab S c) i
  rw [hx] at hnode
  rw [run_reconstruct_encode_cached S (cacheTab S c) i x c hnode (fun v hv =>
    cacheTab_cached S x c hc v ((mem_evalHashAt S i v).1 hv).2.2)]
  rw [recon_honest_eq_observed S i x c hc]

/-- Cache-level conversion theorem used directly by the adversary analysis. -/
theorem run_verify_convert_cached (i j : Fin numCuts) (x : S.graph.Assignment)
    (m : Message) (η : Nonce) (c : Cache)
    (hc : S.graph.CacheConsistent x c) (hsub : evalHashAt S j ⊆ evalHashAt S i)
    (w : BitVec hashBits) (hw : c ⟨msgBits + nonceBits, m ++ η⟩ = some w)
    (hidx : (w.setWidth idxBits).toNat = j.val) :
    run (S.verify (S.publicKey x) m (η,
      convert S i j (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) x)) (observed S i x))) c =
      pure (true,c) := by
  have hx := evalTab_cacheTab S x c hc
  have hcache : ∀ v ∈ evalHashAt S i,
      c ⟨(S.graph.kind v).inLen, (S.graph.kind v).input (S.graph.evalTab x (cacheTab S c))⟩ =
        some (cacheTab S c v ((S.graph.kind v).input (S.graph.evalTab x (cacheTab S c)))) := by
    rw [hx]
    intro v hv
    exact cacheTab_cached S x c hc v ((mem_evalHashAt S i v).1 hv).2.2
  have h := run_verify_convert S i j x (cacheTab S c) m η c hsub hcache w hw hidx
  dsimp only at h
  rw [hx, recon_honest_eq_observed S i x c hc] at h
  exact h

end OptimalOTS.Conversion
