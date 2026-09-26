import Submissions.UpperLeanIsa.FusionAdmissible
import Submissions.UpperLeanIsa.FusionBinding
import Submissions.UpperLeanIsa.Transcript

/-! Cached verification paths with dependency contexts normalized to the final tops. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical
noncomputable section
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Params
variable (P : Params)

def stB (A : OracleAlgorithm.Adversary) (pk : PublicKey) (m₁ : Message) (st : A.State)
    (σ : Option OracleAlgorithm.Signature) : OracleComp Spec Bool := do
  let (m₂,σ₂) ← A.forge st σ
  let ok ← P.verify pk m₂ σ₂
  pure (ok && decide (σ.map (fun s => (m₁,s)) ≠ some (m₂,σ₂)))

def rest₂ (A : OracleAlgorithm.Adversary) (pk : PublicKey) (sk : SecretKey)
    (y : Message × A.State) : OracleComp Spec Bool :=
  P.codec.sign sk y.1 >>= P.stB A pk y.1 y.2

def rest (A : OracleAlgorithm.Adversary) (x : PublicKey × SecretKey) : OracleComp Spec Bool :=
  A.choose x.1 >>= P.rest₂ A x.1 x.2

theorem experiment_eq (A : OracleAlgorithm.Adversary) :
    OracleAlgorithm.experiment P.scheme A = P.keygen >>= P.rest A := rfl

def ChainPath (c : Cache) (t : Tops) (k : Fin 42) (j n : ℕ) (x : Word) : Prop :=
  ∀ i, i < n → (c ⟨896,P.chainInput t k (j+i) (P.chainValue (table c) t k j i x)⟩).isSome

theorem chainValue_succ (f : HashTable) (t : Tops) (k : Fin 42) (j n : ℕ) (x : Word) :
    P.chainValue f t k j (n+1) x = P.chainValue f t k (j+1) n (P.stepValue f t k j x) := rfl

theorem stepValue_of_sub {c c' : Cache} (h : Cache.Sub c c') {t : Tops} {k : Fin 42}
    {j : ℕ} {x : Word} (hx : (c ⟨896,P.chainInput t k j x⟩).isSome) :
    P.stepValue (table c') t k j x = P.stepValue (table c) t k j x :=
  congrArg (P.codec.slice k j) (table_of_sub h hx)

theorem ChainPath.mono {c c' : Cache} (h : Cache.Sub c c') {t : Tops} {k : Fin 42}
    {j n : ℕ} {x : Word} (hp : P.ChainPath c t k j n x) :
    P.ChainPath c' t k j n x ∧ P.chainValue (table c') t k j n x = P.chainValue (table c) t k j n x := by
  have key : ∀ i, i ≤ n → P.chainValue (table c') t k j i x = P.chainValue (table c) t k j i x := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [chainValue_snoc,chainValue_snoc,ih (by omega)]
      exact P.stepValue_of_sub h (hp i (by omega))
  refine ⟨?_,key n le_rfl⟩
  intro i hi
  rw [key i hi.le]
  exact h.isSome (hp i hi)

theorem ChainPath.cached {c : Cache} {t : Tops} {k : Fin 42} {j n : ℕ} {x : Word}
    (hp : P.ChainPath c t k j n x) {i : ℕ} (hji : j ≤ i) (hi : i < j+n) :
    (c ⟨896,P.chainInput t k i (P.chainValue (table c) t k j (i-j) x)⟩).isSome := by
  have h := hp (i-j) (by omega)
  rwa [Nat.add_sub_of_le hji] at h

theorem chainStep_support (t : Tops) (k : Fin 42) (j : ℕ) (x : Word) (c : Cache) :
    ∀ p ∈ support (run (P.chainStep t k j x) c), Cache.Sub c p.2 ∧
      (p.2 ⟨896,P.chainInput t k j x⟩).isSome ∧ p.1 = P.stepValue (table p.2) t k j x := by
  intro p hp
  unfold chainStep at hp
  rw [run_map,support_map,Set.mem_image] at hp
  obtain ⟨q,hq,rfl⟩ := hp
  obtain ⟨hsub,hc⟩ := Layer.Params.run_hash_support _ c q hq
  refine ⟨hsub,Option.isSome_iff_exists.2 ⟨q.1,hc⟩,?_⟩
  exact congrArg (P.codec.slice k j) (table_eq_of_some hc).symm

theorem chain_support (t : Tops) (k : Fin 42) (j n : ℕ) (x : Word) (c : Cache) :
    ∀ p ∈ support (run (P.chain t k j n x) c), Cache.Sub c p.2 ∧
      p.1 = P.chainValue (table p.2) t k j n x ∧ P.ChainPath p.2 t k j n x := by
  induction n generalizing j x c with
  | zero =>
    intro p hp
    rw [show run (P.chain t k j 0 x) c = pure (x,c) from run_pure x c,
      support_pure,Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c,rfl,fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    intro p hp
    rw [chain,run_bind,support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨q,hq,hp⟩ := hp
    obtain ⟨hs₁,hcached,hstep⟩ := P.chainStep_support t k j x c q hq
    obtain ⟨hs₂,hval,hpath⟩ := ih (j+1) q.1 q.2 p hp
    have hst : P.stepValue (table p.2) t k j x = q.1 :=
      (P.stepValue_of_sub hs₂ hcached).trans hstep.symm
    refine ⟨hs₁.trans hs₂,?_,?_⟩
    · rw [chainValue_succ,hst]
      exact hval
    · intro i hi
      cases i with
      | zero => exact hs₂.isSome hcached
      | succ i =>
        rw [chainValue_succ,hst,show j+(i+1)=j+1+i by omega]
        exact hpath i (by omega)

def RootPath (c : Cache) (t : Tops) : List (Fin 3) → BitVec 256 → Prop
  | [],_ => True
  | r::l,st => (c ⟨896,P.rootInput t r st⟩).isSome ∧
      RootPath c t l (table c ⟨896,P.rootInput t r st⟩)

theorem RootPath.mono {c c' : Cache} (h : Cache.Sub c c') (t : Tops)
    (l : List (Fin 3)) (st : BitVec 256) (hp : P.RootPath c t l st) :
    P.RootPath c' t l st ∧ P.rootFromValue (table c') t l st = P.rootFromValue (table c) t l st := by
  induction l generalizing st with
  | nil => exact ⟨trivial,rfl⟩
  | cons r l ih =>
    have he := table_of_sub h hp.1
    obtain ⟨hl,hv⟩ := ih _ hp.2
    constructor
    · exact ⟨h.isSome hp.1,by rw [he]; exact hl⟩
    · rw [rootFromValue,rootFromValue,he]
      exact hv

theorem rootFrom_support (t : Tops) (l : List (Fin 3)) (st : BitVec 256) (c : Cache) :
    ∀ p ∈ support (run (P.rootFrom t l st) c), Cache.Sub c p.2 ∧
      p.1 = P.rootFromValue (table p.2) t l st ∧ P.RootPath p.2 t l st := by
  induction l generalizing st c with
  | nil =>
    intro p hp
    rw [rootFrom,run_pure,support_pure,Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c,rfl,trivial⟩
  | cons r l ih =>
    intro p hp
    rw [rootFrom,run_bind,support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨q,hq,hp⟩ := hp
    obtain ⟨hs₁,hc₁⟩ := Layer.Params.run_hash_support _ c q hq
    obtain ⟨hs₂,hval,hpath⟩ := ih q.1 q.2 p hp
    have hc := hs₂ _ _ hc₁
    have he := table_eq_of_some hc
    refine ⟨hs₁.trans hs₂,?_,Option.isSome_iff_exists.2 ⟨q.1,hc⟩,?_⟩
    · rw [rootFromValue,he]
      exact hval
    · rw [he]
      exact hpath

theorem root_support (t : Tops) (c : Cache) : ∀ p ∈ support (run (P.root t) c),
    Cache.Sub c p.2 ∧ p.1 = P.rootValue (table p.2) t ∧ P.RootPath p.2 t [0,1,2] 0 := by
  intro p hp
  unfold root at hp
  rw [run_map,support_map,Set.mem_image] at hp
  obtain ⟨q,hq,rfl⟩ := hp
  obtain ⟨hsub,hval,hpath⟩ := P.rootFrom_support t [0,1,2] 0 c q hq
  exact ⟨hsub,congrArg (fun z : BitVec 256 => z.extractLsb' 0 128) hval,hpath⟩

def ReconPath (c : Cache) (I : Index) (bits : List Bool) : List (Fin 42) → Tops → Prop
  | [],_ => True
  | k::l,t => P.ChainPath c t k (P.codec.len k - 1 - P.codec.digit I k)
      (P.codec.digit I k) (decodeWord bits k) ∧
    ReconPath c I bits l (Function.update t k.val (P.chainValue (table c) t k
      (P.codec.len k - 1 - P.codec.digit I k) (P.codec.digit I k) (decodeWord bits k)))

theorem ReconPath.mono {c c' : Cache} (h : Cache.Sub c c') (I : Index) (bits : List Bool)
    (l : List (Fin 42)) (t : Tops) (hp : P.ReconPath c I bits l t) :
    P.ReconPath c' I bits l t ∧
      P.reconFromValue (table c') I bits l t = P.reconFromValue (table c) I bits l t := by
  induction l generalizing t with
  | nil => exact ⟨trivial,rfl⟩
  | cons k l ih =>
    obtain ⟨hc,hv⟩ := ChainPath.mono P h hp.1
    obtain ⟨hl,he⟩ := ih _ hp.2
    constructor
    · exact ⟨hc,by rw [hv]; exact hl⟩
    · rw [reconFromValue,reconFromValue,hv]
      exact he

theorem reconFrom_support (I : Index) (bits : List Bool) (l : List (Fin 42)) (t : Tops) (c : Cache) :
    ∀ p ∈ support (run (P.reconFrom I bits l t) c), Cache.Sub c p.2 ∧
      p.1 = P.reconFromValue (table p.2) I bits l t ∧ P.ReconPath p.2 I bits l t := by
  induction l generalizing t c with
  | nil =>
    intro p hp
    rw [reconFrom,run_pure,support_pure,Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c,rfl,trivial⟩
  | cons k l ih =>
    intro p hp
    rw [reconFrom,run_bind,support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨q,hq,hp⟩ := hp
    obtain ⟨hs₁,hval₁,hpath₁⟩ := P.chain_support t k _ _ _ c q hq
    obtain ⟨hs₂,hval₂,hpath₂⟩ := ih (Function.update t k.val q.1) q.2 p hp
    obtain ⟨hpath,hval⟩ := ChainPath.mono P hs₂ hpath₁
    have he := hval.trans hval₁.symm
    refine ⟨hs₁.trans hs₂,?_,hpath,?_⟩
    · rw [reconFromValue,he]
      exact hval₂
    · rw [he]
      exact hpath₂

theorem chainValue_context (f : HashTable) (t t' : Tops) (k : Fin 42) (j n : ℕ) (x : Word)
    (ht : ∀ u : Fin 6, owner k = some u → ∀ d ∈ children u, t d = t' d) :
    P.chainValue f t k j n x = P.chainValue f t' k j n x := by
  induction n generalizing j x with
  | zero => rfl
  | succ n ih =>
    rw [chainValue,chainValue]
    have hs : P.stepValue f t k j x = P.stepValue f t' k j x :=
      congrArg (fun q => P.codec.slice k j (f ⟨896,q⟩)) (Params.chainInput_congr t t' k j x ht)
    rw [hs]
    exact ih (j+1) _

theorem ChainPath.context (c : Cache) (t t' : Tops) (k : Fin 42) (j n : ℕ) (x : Word)
    (ht : ∀ u : Fin 6, owner k = some u → ∀ d ∈ children u, t d = t' d)
    (hp : P.ChainPath c t k j n x) : P.ChainPath c t' k j n x := by
  intro i hi
  rw [← P.chainValue_context (table c) t t' k j i x ht,
    ← Params.chainInput_congr t t' k (j+i) _ ht]
  exact hp i hi

theorem reconFromValue_preserves (f : HashTable) (I : Index) (bits : List Bool)
    (l : List (Fin 42)) (t : Tops) (d : ℕ) (hd : d ∉ l.map Fin.val) :
    P.reconFromValue f I bits l t d = t d := by
  induction l generalizing t with
  | nil => rfl
  | cons k l ih =>
    have he : d ≠ k.val := fun he => hd (by simp [he])
    have hl : d ∉ l.map Fin.val := fun h => hd (by simp [h])
    rw [reconFromValue,ih _ hl,Function.update_of_ne he]

theorem reconFrom_normalized (c : Cache) (I : Index) (bits : List Bool) (l : List (Fin 42))
    (hl : l.Pairwise (fun k k' => evaluationRank k.val < evaluationRank k'.val)) (t : Tops)
    (hp : P.ReconPath c I bits l t) :
    let t' := P.reconFromValue (table c) I bits l t
    ∀ k ∈ l, P.ChainPath c t' k (P.codec.len k - 1 - P.codec.digit I k)
      (P.codec.digit I k) (decodeWord bits k) ∧
      P.chainValue (table c) t' k (P.codec.len k - 1 - P.codec.digit I k)
        (P.codec.digit I k) (decodeWord bits k) = t' k.val := by
  induction l generalizing t with
  | nil => simp
  | cons k l ih =>
    obtain ⟨hbefore,hl⟩ := List.pairwise_cons.mp hl
    let t' := P.reconFromValue (table c) I bits (k::l) t
    have hdep : ∀ u : Fin 6, owner k = some u → ∀ d ∈ children u, t d = t' d := by
      intro u hu d hd
      apply (P.reconFromValue_preserves (table c) I bits (k::l) t d ?_).symm
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
    have hknot : k.val ∉ l.map Fin.val := by
      rintro hmem
      obtain ⟨k',hk',he⟩ := List.mem_map.mp hmem
      have hh := hbefore k' hk'
      rw [he] at hh
      omega
    have htop : t' k.val = P.chainValue (table c) t k
        (P.codec.len k - 1 - P.codec.digit I k) (P.codec.digit I k) (decodeWord bits k) := by
      change P.reconFromValue (table c) I bits l (Function.update t k.val _) k.val = _
      rw [P.reconFromValue_preserves _ _ _ _ _ _ hknot,Function.update_self]
    intro t'' k' hk'
    rcases List.mem_cons.mp hk' with he | hk'
    · subst k'
      exact ⟨ChainPath.context P c t t' k _ _ _ hdep hp.1,
        (P.chainValue_context (table c) t t' k _ _ _ hdep).symm.trans htop.symm⟩
    · exact ih hl _ hp.2 k' hk'

def reconWords (f : HashTable) (I : Index) (bits : List Bool) : Tops :=
  P.reconFromValue f I bits chainOrder (fun _ => 0)

structure Accepts (c : Cache) (pk : PublicKey) (m : Message) (bits : List Bool) : Prop where
  length : bits.length = sigBits
  idx_cached : (c ⟨896,P.codec.idxInput m (decodeNonce bits) pk⟩).isSome
  accepted : P.codec.Accepted (P.codec.idxValue (table c) m (decodeNonce bits) pk)
  reconstruction : P.ReconPath c (P.codec.idxValue (table c) m (decodeNonce bits) pk)
    bits chainOrder (fun _ => 0)
  rootPath : P.RootPath c (P.reconWords (table c) (P.codec.idxValue (table c) m (decodeNonce bits) pk)
    bits) [0,1,2] 0
  root : P.rootValue (table c)
    (P.reconWords (table c) (P.codec.idxValue (table c) m (decodeNonce bits) pk) bits) = pk

theorem verify_support (pk : PublicKey) (m : Message) (bits : List Bool) (c : Cache) :
    ∀ p ∈ support (run (P.verify pk m bits) c), Cache.Sub c p.2 ∧
      (p.1 = true → P.Accepts p.2 pk m bits) := by
  intro p hp
  by_cases hlen : bits.length = sigBits
  · have ev : P.verify pk m bits = (P.codec.index m (decodeNonce bits) pk >>= fun I =>
        if ¬ P.codec.Accepted I then pure false else
          P.reconFrom I bits chainOrder (fun _ => 0) >>= fun tops =>
            P.root tops >>= fun r => pure (r == pk)) := by
      simp only [verify,hlen,ne_eq,not_true_eq_false,if_false]
    rw [ev,run_bind,support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨q₀,hq₀,hp⟩ := hp
    obtain ⟨hs₀,hidx,hI⟩ := P.codec.index_support m (decodeNonce bits) pk c q₀ hq₀
    by_cases hacc : P.codec.Accepted q₀.1
    · rw [if_neg (not_not.mpr hacc),run_bind,support_bind] at hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨q,hq,hp⟩ := hp
      rw [run_bind,support_bind] at hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨r,hr,hp⟩ := hp
      rw [run_pure,support_pure,Set.mem_singleton_iff] at hp
      subst hp
      obtain ⟨hs₁,hrec,hpath⟩ := P.reconFrom_support q₀.1 bits chainOrder _ q₀.2 q hq
      obtain ⟨hs₂,hroot,hrpath⟩ := P.root_support q.1 q.2 r hr
      have hIr : P.codec.idxValue (table r.2) m (decodeNonce bits) pk = q₀.1 := by
        rw [hI]
        exact congrArg indexSlice (table_of_sub (hs₁.trans hs₂) hidx)
      obtain ⟨hpath',hrec'⟩ := ReconPath.mono P hs₂ q₀.1 bits chainOrder _ hpath
      have he : P.reconWords (table r.2) q₀.1 bits = q.1 := hrec'.trans hrec.symm
      refine ⟨hs₀.trans (hs₁.trans hs₂),fun hok => ?_⟩
      refine ⟨hlen,(hs₁.trans hs₂).isSome hidx,by rw [hIr]; exact hacc,?_,?_,?_⟩
      · rw [hIr]
        exact hpath'
      · rw [hIr,he]
        exact hrpath
      · rw [hIr,he]
        exact hroot.symm.trans (eq_of_beq hok)
    · rw [if_pos hacc,run_pure,support_pure,Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hs₀,fun h => by cases h⟩
  · rw [P.verify_of_length_ne pk m bits hlen,run_pure,support_pure,Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨Cache.Sub.refl c,fun h => by cases h⟩

theorem stB_support (A : OracleAlgorithm.Adversary) (pk : PublicKey) (m₁ : Message) (st : A.State)
    (σ : Option OracleAlgorithm.Signature) (c : Cache) :
    ∀ p ∈ support (run (P.stB A pk m₁ st σ) c), Cache.Sub c p.2 ∧ (p.1 = true →
      ∃ m₂ σ₂, σ.map (fun s => (m₁,s)) ≠ some (m₂,σ₂) ∧ P.Accepts p.2 pk m₂ σ₂) := by
  intro p hp
  unfold stB at hp
  rw [run_bind,support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨⟨m₂,σ₂⟩,c₁⟩,h₁,hp⟩ := hp
  have hs₁ := sub_of_mem_support_run _ c _ h₁
  dsimp only at hp hs₁
  rw [run_bind,support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨ok,c₂⟩,h₂,hp⟩ := hp
  obtain ⟨hs₂,hver⟩ := P.verify_support pk m₂ σ₂ c₁ ⟨ok,c₂⟩ h₂
  dsimp only at hp hs₂ hver
  rw [run_pure,support_pure,Set.mem_singleton_iff] at hp
  subst hp
  refine ⟨hs₁.trans hs₂,fun hok => ?_⟩
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hok
  exact ⟨m₂,σ₂,hok.2,hver hok.1⟩

end Params
end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
