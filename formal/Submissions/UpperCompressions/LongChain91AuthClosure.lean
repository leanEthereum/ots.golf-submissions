import Submissions.UpperCompressions.LongChain91Auth

/-!
# Authentication-event closure for the cost-90 shared-DAG graph

An accepting reconstruction is followed downward from the public root along
reconstructed nodes.  At each hash node the forged input either differs from
the honest one, which is a spurious binding `Spr`, or equals it, so every
input of that node is honest again.  The walk needs only the parent sets of
the DAG, not a unique consumer per node.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag
open Name

/-! ## Visited nodes of the DAG -/

theorem evaluated_iff {A : Finset Name} {n : Name} :
    Evaluated A n ↔ graph.Visited (fins A) n.fin ∧ n ∉ A := Iff.rfl

theorem visited_of_mem_parents {A : Finset Name} {m n : Name}
    (hm : Evaluated A m) (hn : n ∈ parents m) : graph.Visited (fins A) n.fin :=
  Graph.Visited.parent hm.1 (fun h => hm.2 ((mem_fins_embedding A m).1 h))
    ((mem_graph_parents_iff n m).2 hn)

theorem evaluated_of_mem_parents {A : Finset Name} {m n : Name}
    (hm : Evaluated A m) (hn : n ∈ parents m) (hnA : n ∉ A) : Evaluated A n :=
  ⟨visited_of_mem_parents hm hn, hnA⟩

theorem evaluated_or_mem_of_mem_parents {A : Finset Name} {m n : Name}
    (hm : Evaluated A m) (hn : n ∈ parents m) : Evaluated A n ∨ n ∈ A := by
  by_cases hnA : n ∈ A
  · exact Or.inr hnA
  · exact Or.inl (evaluated_of_mem_parents hm hn hnA)

/-- A visited node is the root or an input of an evaluated node. -/
theorem visited_cases {A : Finset Name} {n : Name}
    (hv : graph.Visited (fins A) n.fin) :
    n = Name.rh ∨ ∃ m, n ∈ parents m ∧ Evaluated A m := by
  have key : ∀ x : Fin graph.size, graph.Visited (fins A) x → x = n.fin →
      n = Name.rh ∨ ∃ m, n ∈ parents m ∧ Evaluated A m := by
    intro x hx e
    cases hx with
    | root => exact Or.inl (Name.fin_injective e.symm)
    | parent hw hwA hmem =>
        rename_i w
        obtain ⟨m, rfl⟩ : ∃ m : Name, m.fin = w := ⟨_, Name.fin_ofFin w⟩
        subst e
        exact Or.inr ⟨m, (mem_graph_parents_iff n m).1 hmem,
          hw, fun h => hwA ((mem_fins_embedding A m).2 h)⟩
  exact key _ hv rfl

theorem not_mem_of_cut_len_ne {A : Finset Name} (hA : IsCut A)
    {n : Name} (hn : n.len ≠ 129) : n ∉ A :=
  fun hm => hn (hA.values n hm)

theorem evaluated_rh_of_isCut {A : Finset Name} (hA : IsCut A) : Evaluated A Name.rh :=
  ⟨Graph.Visited.root, not_mem_of_cut_len_ne hA (by simp [Name.len])⟩

/-- A hash node is visited exactly when its value node is evaluated. -/
theorem visited_hash_iff {A : Finset Name} {v h : Name} (hh : hashOf v = some h) :
    graph.Visited (fins A) h.fin ↔ Evaluated A v := by
  constructor
  · intro hv
    rcases visited_cases hv with e | ⟨m, hm, hmE⟩
    · exact absurd e (ne_rh_of_hashOf hh)
    · rwa [consumer_of_hashOf hh hm] at hmE
  · intro hv
    exact visited_of_mem_parents hv (mem_parents_hashOf hh)

/-- A compression input is visited exactly when its hash node is evaluated. -/
theorem visited_compress_iff {A : Finset Name} {h p : Name}
    (hp : hashParent h = some p) :
    graph.Visited (fins A) p.fin ↔ Evaluated A h := by
  constructor
  · intro hv
    rcases visited_cases hv with e | ⟨m, hm, hmE⟩
    · subst e
      cases h <;> simp [hashParent] at hp
    · rwa [consumer_of_hashParent hp hm] at hmE
  · intro hv
    exact visited_of_mem_parents hv (mem_parents_hashParent hp)

/-! ## Reconstruction equations by concrete name -/

def yv (y : graph.Assignment) (n : Name) : BitVec n.len :=
  (y n.fin).cast (graph_len_fin n)

theorem sigma_cast {a b : ℕ} (h : a = b) (x : BitVec a) :
    (⟨a, x⟩ : Σ k : ℕ, BitVec k) = ⟨b, x.cast h⟩ := by
  subst h
  rfl

theorem lowPk_cast_eq {a b : ℕ} (h : a = b) (x : BitVec a) :
    lowPk (x.cast h) = lowPk x := by
  subst h
  rfl

theorem lowWord_cast_eq {a b : ℕ} (h : a = b) (x : BitVec a) :
    lowWord (x.cast h) = lowWord x := by
  subst h
  rfl

theorem setWidth_cast_eq {a b : ℕ} (h : a = b) (x : BitVec a) (k : ℕ) :
    (x.cast h).setWidth k = x.setWidth k := by
  subst h
  rfl

theorem lowWord_129 (x : BitVec 129) : lowWord x = x := BitVec.setWidth_eq x

theorem lowWord_eq_cast {m : ℕ} (h : m = 129) (x : BitVec m) :
    lowWord x = x.cast h := by
  subst h
  exact BitVec.setWidth_eq x

theorem graph_kind_hash {h p : Name} (hp : hashParent h = some p) :
    ∃ (hlt : p.fin < h.fin) (hl : graph.len h.fin = hashBits),
      graph.kind h.fin = .hash p.fin hlt hl := by
  rw [graph_kind_fin]
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> exact ⟨_, _, rfl⟩

theorem graph_kind_det {n : Name} (hc : n.cost = 0)
    (hs : ∀ b k, n ≠ Name.src b k) :
    ∃ hlt hf, graph.kind n.fin =
      .det (Name.parentFins n) hlt
        (fun x => (detVal n x).cast (graph_len_fin n).symm) hf := by
  rw [graph_kind_fin]
  cases n
  all_goals first
    | exact (hs _ _ rfl).elim
    | exact ⟨_, _, rfl⟩
    | (exfalso; simp [Name.cost] at hc)

section Recon

variable {A : Finset Name} {d : Cache} {given y : graph.Assignment}

theorem yv_mem (hy : graph.ReconEqs d (fins A) given y)
    {n : Name} (hn : n ∈ A) :
    yv y n = (given n.fin).cast (graph_len_fin n) := by
  unfold yv
  rw [(hy n.fin).1 ((mem_fins_embedding A n).mpr hn)]

theorem recon_evaluated (hy : graph.ReconEqs d (fins A) given y)
    {n : Name} (he : Evaluated A n) :
    (∀ p hp hl, graph.kind n.fin = .hash p hp hl →
        ∃ w, d ⟨graph.len p, y p⟩ = some w ∧ y n.fin = w.cast hl.symm) ∧
      (∀ ps hlt f hf, graph.kind n.fin = .det ps hlt f hf → y n.fin = f y) ∧
      (graph.kind n.fin = .source → y n.fin = 0) := by
  exact (hy n.fin).2.2
    (fun h => he.2 ((mem_fins_embedding A n).mp h)) he.1

/-- The cached answer at the reconstructed input of an evaluated hash node. -/
theorem yv_hash_setWidth (hy : graph.ReconEqs d (fins A) given y)
    {h p : Name} (hp : hashParent h = some p) (he : Evaluated A h) :
    ∃ w, d ⟨p.len, yv y p⟩ = some w ∧
      ∀ k, (yv y h).setWidth k = w.setWidth k := by
  obtain ⟨hlt, hl, hk⟩ := graph_kind_hash hp
  obtain ⟨w, hw, hyw⟩ := (recon_evaluated hy he).1 _ _ _ hk
  refine ⟨w, ?_, fun k => ?_⟩
  · rw [sigma_cast (graph_len_fin p) (y p.fin)] at hw
    exact hw
  · unfold yv
    rw [setWidth_cast_eq, hyw, setWidth_cast_eq]

theorem yv_hash (hy : graph.ReconEqs d (fins A) given y)
    {h p : Name} (hp : hashParent h = some p) (he : Evaluated A h) :
    ∃ w, d ⟨p.len, yv y p⟩ = some w ∧
      lowWord w = lowWord (yv y h) := by
  obtain ⟨w, hw, hk⟩ := yv_hash_setWidth hy hp he
  exact ⟨w, hw, (hk 129).symm⟩

theorem yv_det (hy : graph.ReconEqs d (fins A) given y)
    {n : Name} (he : Evaluated A n) (hc : n.cost = 0)
    (hs : ∀ b k, n ≠ Name.src b k) : yv y n = detVal n y := by
  obtain ⟨hlt, hf, hk⟩ := graph_kind_det hc hs
  have hv := (recon_evaluated hy he).2.1 _ _ _ _ hk
  unfold yv
  rw [hv]
  exact cast_cast_eq _ _ _

theorem yv_compress (hy : graph.ReconEqs d (fins A) given y)
    {h p : Name} (hp : hashParent h = some p) (he : Evaluated A p) :
    yv y p = detVal p y :=
  yv_det hy he (cost_hashParent hp) (hashParent_ne_src hp)

theorem lowWord_yv_value (hy : graph.ReconEqs d (fins A) given y)
    {v h : Name} (hh : hashOf v = some h) (he : Evaluated A v) :
    lowWord (yv y v) = lowWord (y h.fin) := by
  rw [yv_det hy he (cost_of_hashOf hh) (not_src_of_hashOf hh)]
  exact lowWord_detVal_value hh y

end Recon

theorem tagNat_yv {A : Finset Name} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    {h p : Name} (hp : hashParent h = some p) (he : Evaluated A p) :
    tagNat ⟨p.len, yv y p⟩ = h.idx := by
  rw [yv_compress hy hp he]
  exact tagNat_detVal_of_hashParent hp y

/-! ## The descent from the root -/

/-- Honest agreement at a reconstructed node: the binding bits at a hash node,
the full value elsewhere. -/
def Good (y : graph.Assignment) (ξ : Rec) (n : Name) : Prop :=
  if (hashParent n).isSome then
    (yv y n).setWidth (bindingWidth n) = bindingValue n (ξ.2 n.fin)
  else yv y n = val ξ n

theorem good_of_not_hash {y : graph.Assignment} {ξ : Rec} {n : Name}
    (hn : hashParent n = none) : Good y ξ n ↔ yv y n = val ξ n := by
  simp [Good, hn]

theorem good_of_hash {y : graph.Assignment} {ξ : Rec} {h p : Name}
    (hp : hashParent h = some p) :
    Good y ξ h ↔ (yv y h).setWidth (bindingWidth h) = bindingValue h (ξ.2 h.fin) := by
  simp [Good, hp]

theorem hashParent_eq_none_of_len {n : Name} (hn : n.len = 129) :
    hashParent n = none := by
  rcases hp : hashParent n with _ | p
  · rfl
  · rw [len_of_hashParent hp] at hn
    omega

theorem eq_of_lowWord_yv_val {y : graph.Assignment} {ξ : Rec} {n : Name}
    (hn : n.len = 129) (h : lowWord (y n.fin) = lowWord (graph.evalRec ξ n.fin)) :
    yv y n = val ξ n := by
  apply eq_of_lowWord_eq hn
  unfold yv val
  rw [lowWord_cast_eq, lowWord_cast_eq]
  exact h

/-- One step of the descent: honest agreement passes from an evaluated node
to its inputs, unless a spurious binding occurs. -/
theorem good_step {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    {m n : Name} (hmE : Evaluated A m) (hg : Good y ξ m) (hn : n ∈ parents m) :
    Spr d ξ ∨ Good y ξ n := by
  rcases mem_parents_cases hn with ⟨p, hp, rfl⟩ | hv | ⟨h, hp, hkind⟩
  · rw [good_of_hash hp] at hg
    have hpE : Evaluated A n :=
      evaluated_of_mem_parents hmE hn
        (not_mem_of_cut_len_ne hA (len_hashParent_ne_129 hp))
    obtain ⟨w, hd, hw⟩ := yv_hash_setWidth hy hp hmE
    by_cases e : yv y n = val ξ n
    · exact Or.inr ((good_of_not_hash (hashParent_hashParent hp)).2 e)
    · exact Or.inl ⟨m, n, hp, yv y n, e, tagNat_yv hy hp hpE, w, hd,
        (hw _).symm.trans hg⟩
  · rw [good_of_not_hash (hashParent_value hv)] at hg
    obtain ⟨p, hp⟩ := hashParent_of_hashOf hv
    right
    rw [good_of_hash hp]
    have hbw : bindingWidth n = 129 := if_neg (ne_rh_of_hashOf hv)
    show (yv y n).setWidth (bindingWidth n) = (ξ.2 n.fin).setWidth (bindingWidth n)
    rw [hbw]
    change lowWord (yv y n) = lowWord (ξ.2 n.fin)
    unfold yv
    rw [lowWord_cast_eq, ← lowWord_yv_value hy hv hmE, hg,
      lowWord_val_value hv]
  · rw [good_of_not_hash (hashParent_hashParent hp)] at hg
    have hnlen := len_of_mem_parents_compress hp hn
    right
    rw [good_of_not_hash (hashParent_eq_none_of_len hnlen)]
    rw [yv_compress hy hp hmE, val_hashParent hp] at hg
    exact eq_of_lowWord_yv_val hnlen (compress_inj hp hg hn)

/-- Every visited node of an accepting reconstruction is honest, unless a
spurious binding occurs. -/
theorem descent {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    (hacc : lowPk (yv y Name.rh) = pkOf ξ) {n : Name}
    (hv : graph.Visited (fins A) n.fin) : Spr d ξ ∨ Good y ξ n := by
  suffices key : ∀ x, graph.Visited (fins A) x →
      Spr d ξ ∨ Good y ξ (Name.ofFin x) by
    simpa only [Name.ofFin_fin] using key n.fin hv
  intro x hx
  induction hx with
  | root =>
      right
      change Good y ξ (Name.ofFin Name.rh.fin)
      rw [Name.ofFin_fin, good_of_hash (p := Name.rc) rfl]
      have hbw : bindingWidth Name.rh = 128 := if_pos rfl
      show (yv y Name.rh).setWidth (bindingWidth Name.rh) =
        (ξ.2 Name.rh.fin).setWidth (bindingWidth Name.rh)
      rw [hbw]
      exact hacc
  | parent hw hwA hmem ih =>
      rename_i w v
      rcases ih with hs | hg
      · exact Or.inl hs
      obtain ⟨m, rfl⟩ : ∃ m : Name, m.fin = w := ⟨_, Name.fin_ofFin w⟩
      obtain ⟨n, rfl⟩ : ∃ n : Name, n.fin = v := ⟨_, Name.fin_ofFin v⟩
      rw [Name.ofFin_fin] at hg ⊢
      exact good_step hA hy ⟨hw, fun h => hwA ((mem_fins_embedding A m).2 h)⟩
        hg ((mem_graph_parents_iff n m).1 hmem)

/-- A disclosed value of an accepting reconstruction is honest, unless a
spurious binding occurs. -/
theorem descent_mem {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    (hacc : lowPk (yv y Name.rh) = pkOf ξ) {a : Name} (ha : a ∈ A) :
    Spr d ξ ∨ yv y a = val ξ a := by
  rcases descent hA hy hacc (hA.visited_of_mem ha) with hs | hg
  · exact Or.inl hs
  · exact Or.inr ((good_of_not_hash (hashParent_eq_none_of_len (hA.values a ha))).1 hg)

/-- The honest input of an evaluated hash node is queried, unless a spurious
binding occurs. -/
theorem descent_query {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    (hacc : lowPk (yv y Name.rh) = pkOf ξ) {h p : Name}
    (hp : hashParent h = some p) (he : Evaluated A h) :
    Spr d ξ ∨ (d (pointOf ξ h p)).isSome := by
  rcases descent hA hy hacc (visited_of_mem_parents he (mem_parents_hashParent hp))
    with hs | hg
  · exact Or.inl hs
  · right
    rw [good_of_not_hash (hashParent_hashParent hp)] at hg
    obtain ⟨w, hd, -⟩ := yv_hash hy hp he
    unfold pointOf
    rw [← hg, hd]
    rfl

/-! ## Terminal no-signature authentication event -/

/-- If no disclosure set has been fixed, every accepting reconstruction either
uses a spurious hash image or queries the honest root-hash input. -/
theorem events_none {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    (hacc : lowPk (yv y Name.rh) = pkOf ξ) :
    Spr d ξ ∨ Cache.Hits d (kc ξ) := by
  rcases descent_query hA hy hacc (h := Name.rh) (p := Name.rc) rfl
      (evaluated_rh_of_isCut hA) with hs | hq
  · exact Or.inl hs
  · right
    refine ⟨pointOf ξ Name.rh Name.rc, ?_, hq⟩
    rw [kc_isSome_iff]
    exact ⟨Name.rh, Name.rc, rfl, rfl⟩

/-- The concrete verifier's public-key check is the low 128-bit endpoint of
the reconstructed root value. -/
theorem accepted_lowPk (ξ : Rec) (y : graph.Assignment)
    (h : scheme.publicKey y = pkOf ξ) :
    lowPk (yv y Name.rh) = pkOf ξ := by
  unfold yv
  rw [lowPk_cast_eq]
  exact h

/-- Every accepting verification in the failed-signature branch reaches one
of the two authentication events charged by `authPotential _ none`. -/
theorem accepted_none_event (ξ : Rec) (m : Message)
    (σ : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (scheme.verify (pkOf ξ) m σ) c)) :
    Spr d ξ ∨ Cache.Hits d (kc ξ) := by
  obtain ⟨_, hh⟩ :=
    WeightedScheme.verify_support scheme (pkOf ξ) m σ c (true, d) h
  obtain ⟨_w, _hw, i, _hi, _hlen, y, hy, hpk⟩ := hh rfl
  exact events_none (isCut_of_mem_family (setsName_mem i)) hy
    (accepted_lowPk ξ y hpk)

/-- Pointwise indicator domination at an accepting terminal verifier state. -/
theorem accepted_none_indicator (ξ : Rec) (m : Message)
    (σ : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (scheme.verify (pkOf ξ) m σ) c)) :
    (1 : ℝ≥0∞) ≤ ind (Cache.Hits d (kc ξ)) + ind (Spr d ξ) := by
  rcases accepted_none_event ξ m σ c d h with hs | hh
  · rw [show ind (Spr d ξ) = 1 by simp [ind, hs]]
    exact le_add_self
  · rw [show ind (Cache.Hits d (kc ξ)) = 1 by simp [ind, hh]]
    exact le_self_add

/-- The concrete terminal expectation bound used by both actual-game budget
branches: verifier success is dominated by the two authentication indicators. -/
theorem accepted_none_expected (ξ : Rec) (m : Message)
    (σ : WeightedScheme.Signature) (c : Cache) :
    E (run (scheme.verify (pkOf ξ) m σ) c)
        (fun p => if p.1 = true then 1 else 0) ≤
      E (run (scheme.verify (pkOf ξ) m σ) c)
        (fun p => ind (Cache.Hits p.2 (kc ξ)) + ind (Spr p.2 ξ)) := by
  apply expectedValue_mono_of_support
  rintro ⟨b, d⟩ hd
  cases b
  · simp
  · exact accepted_none_indicator ξ m σ c d hd

#print axioms visited_cases
#print axioms descent
#print axioms events_none
#print axioms accepted_none_event
#print axioms accepted_none_expected

end OptimalOTS.WeightedConstruction.LongChain91
