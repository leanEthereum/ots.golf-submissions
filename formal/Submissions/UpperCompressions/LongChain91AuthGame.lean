import Submissions.UpperCompressions.LongChain91CachedRow
import Submissions.UpperCompressions.LongChain91Auth

/-!
# Authentication-event closure for the cost-88 shared-DAG graph

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

end OptimalOTS.WeightedConstruction.LongChain91

/-!
# Authentication game bridge for the cost-91 long-chain construction

This module proves the two hidden-input charges and closes the same-cut,
changed-payload route from the descent of `LongChain91AuthClosure`.  The
hidden-input charge resamples the record coordinate behind the exclusive kid
of a hidden hash node: that kid is read by no other node, so it stays hidden
after signing even though other kids of the node are shared.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag
open Name

/-! ## Generic authentication-potential algebra -/

theorem sumW_mono {T T' : Finset Rec} (h : T ⊆ T') :
    sumW T ≤ sumW T' :=
  Finset.sum_le_sum_of_subset h

theorem ind_or_le (p r : Prop) : ind (p ∨ r) ≤ ind p + ind r := by
  unfold ind
  by_cases hp : p <;> by_cases hr : r <;> simp [hp, hr]

theorem w_mul_ind_le (p : Prop) [Decidable p] :
    w * ind p ≤ if p then w else 0 := by
  unfold ind
  split_ifs <;> simp

theorem sum_w_mul_le_add_charge (delta : ℝ≥0∞) (T : Finset Rec)
    (a b : Rec → ℝ≥0∞) (h : ∀ xi ∈ T, a xi ≤ b xi + delta) :
    ∑ xi ∈ T, w * a xi ≤
      ∑ xi ∈ T, w * b xi + delta * sumW T := by
  unfold sumW
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun xi hxi => ?_
  rw [mul_comm delta w, ← mul_add]
  exact mul_le_mul_right (h xi hxi) w

/-- A fresh answer can create a hit only at the queried point. -/
theorem hits_avg_le (T : Finset Rec) (f : Rec → Cache)
    (c : Cache) (q : Query) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ xi ∈ T, w * ind (Cache.Hits (c.cacheQuery q u) (f xi)) ≤
      ∑ xi ∈ T, w * ind (Cache.Hits c (f xi)) +
        ∑ xi ∈ T, w * ind ((f xi q).isSome) := by
  rw [avg_sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun xi _ => ?_
  rw [← mul_add]
  refine mul_le_mul_right ?_ w
  calc
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
          ind (Cache.Hits (c.cacheQuery q u) (f xi))
        ≤ ∑ _u : BitVec hashBits,
            (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
              (ind (Cache.Hits c (f xi)) + ind ((f xi q).isSome)) := by
          refine Finset.sum_le_sum fun u _ => mul_le_mul_right ?_ _
          rw [ind_congr (Cache.hits_cacheQuery c (f xi) q u)]
          exact ind_or_le _ _
    _ = _ := sum_inv_card_mul _

theorem spr_avg_le (T : Finset Rec) (c : Cache) (q : Query)
    (hq : c q = none) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ xi ∈ T, w * ind (Spr (c.cacheQuery q u) xi) ≤
      ∑ xi ∈ T, w * ind (Spr c xi) +
        (ε * blockCost q.1) * sumW T := by
  rw [avg_sum_comm]
  exact sum_w_mul_le_add_charge (ε * blockCost q.1) T _ _
    (fun xi _ => spr_charge c xi q hq)

/-! The only missing input to the charge algebra is closure of the concrete
record fibers under resampling the coordinate read by a hidden hash input. -/

def InitialHitsCharge : Prop :=
  ∀ (pk : BitVec 128) (q : Query),
    ∑ xi ∈ fiberA pk, (if (kc xi q).isSome then w else 0) ≤
      ε * sumW (fiberA pk)

def SignedHitsCharge : Prop :=
  ∀ (A : Finset Name), IsCut A → ∀ (dt : Data) (q : Query),
    ∑ xi ∈ fiberB A dt,
        (if (fHid (some A) xi q).isSome then w else 0) ≤
      ε * sumW (fiberB A dt)

theorem hits_charge_A'_of (hbase : InitialHitsCharge) (pk : BitVec 128)
    {T : Finset Rec} (hT : T ⊆ fiberA pk) (q : Query) :
    ∑ xi ∈ T, w * ind ((kc xi q).isSome) ≤
      ε * sumW (fiberA pk) := by
  calc
    ∑ xi ∈ T, w * ind ((kc xi q).isSome)
        ≤ ∑ xi ∈ T, (if (kc xi q).isSome then w else 0) :=
          Finset.sum_le_sum fun _ _ => w_mul_ind_le _
    _ ≤ ∑ xi ∈ fiberA pk, (if (kc xi q).isSome then w else 0) :=
      Finset.sum_le_sum_of_subset hT
    _ ≤ ε * sumW (fiberA pk) := hbase pk q

theorem hits_charge_B'_of (hbase : SignedHitsCharge)
    {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt) (q : Query) :
    ∑ xi ∈ T, w * ind ((fHid (some Ac) xi q).isSome) ≤
      ε * sumW (fiberB Ac dt) := by
  calc
    ∑ xi ∈ T, w * ind ((fHid (some Ac) xi q).isSome)
        ≤ ∑ xi ∈ T,
            (if (fHid (some Ac) xi q).isSome then w else 0) :=
          Finset.sum_le_sum fun _ _ => w_mul_ind_le _
    _ ≤ ∑ xi ∈ fiberB Ac dt,
        (if (fHid (some Ac) xi q).isSome then w else 0) :=
      Finset.sum_le_sum_of_subset hT
    _ ≤ ε * sumW (fiberB Ac dt) := hbase Ac hAc dt q

theorem authPotential_charge_of (hbase : SignedHitsCharge)
    {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt)
    (c : Cache) (q : Query) (hq : c q = none) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      authPotential T (some Ac) (c.cacheQuery q u)) ≤
      authPotential T (some Ac) c +
        authRate * sumW (fiberB Ac dt) * queryCost (.inr q) := by
  simp only [authPotential_eq, mul_add, Finset.sum_add_distrib]
  have hh := (hits_avg_le T (fHid (some Ac)) c q).trans
    (add_le_add_right (hits_charge_B'_of hbase hAc dt hT q) _)
  have hs := (spr_avg_le T c q hq).trans
    (add_le_add_right
      (mul_le_mul_right (sumW_mono hT) (ε * blockCost q.1)) _)
  have hc := mul_le_mul_right (authentication_charge_budget q)
    (sumW (fiberB Ac dt))
  calc
    _ ≤ ((∑ xi ∈ T,
          w * ind (Cache.Hits c (fHid (some Ac) xi))) +
          ε * sumW (fiberB Ac dt)) +
        ((∑ xi ∈ T, w * ind (Spr c xi)) +
          (ε * blockCost q.1) * sumW (fiberB Ac dt)) :=
      add_le_add hh hs
    _ = ((∑ xi ∈ T,
          w * ind (Cache.Hits c (fHid (some Ac) xi))) +
          ∑ xi ∈ T, w * ind (Spr c xi)) +
        (ε + ε * blockCost q.1) * sumW (fiberB Ac dt) := by
      ring
    _ ≤ _ := by
      apply add_le_add_right
      simpa only [authRate, queryCost, mul_assoc, mul_comm, mul_left_comm]
        using hc

/-! ## Coordinate resampling -/

def updSrc (xi : Rec) (b : Fin 3) (k : Fin 14) (z : BitVec 129) : Rec :=
  (Function.update xi.1 (Name.src b k).fin
    (z.cast (graph_len_fin (Name.src b k)).symm), xi.2)

def updHash (xi : Rec) (s : Name) (z : BitVec 256) : Rec :=
  (xi.1, Function.update xi.2 s.fin z)

theorem updHash_snd_self (xi : Rec) (s : Name) (z : BitVec 256) :
    (updHash xi s z).2 s.fin = z :=
  Function.update_self _ _ _

theorem updHash_snd_ne (xi : Rec) (s : Name) (z : BitVec 256)
    {n : Name} (h : n ≠ s) : (updHash xi s z).2 n.fin = xi.2 n.fin := by
  simp only [updHash]
  exact Function.update_of_ne (fun e => h (Name.fin_injective e)) _ _

theorem updSrc_snd (xi : Rec) (b : Fin 3) (k : Fin 14) (z : BitVec 129) :
    (updSrc xi b k z).2 = xi.2 := rfl

theorem updSrc_fst_self (xi : Rec) (b : Fin 3) (k : Fin 14) (z : BitVec 129) :
    (updSrc xi b k z).1 (Name.src b k).fin =
      z.cast (graph_len_fin (Name.src b k)).symm :=
  Function.update_self _ _ _

theorem val_updSrc_self (xi : Rec) (b : Fin 3) (k : Fin 14) (z : BitVec 129) :
    val (updSrc xi b k z) (Name.src b k) = z := by
  rw [val_src, updSrc_fst_self]
  exact cast_cast_eq _ _ _

theorem coordOf_ne_rh (h : Name) (hh : h.cost ≠ 0) : coordOf h ≠ Name.rh := by
  cases h <;> simp [Name.cost] at hh
  · simp only [coordOf]
    split_ifs <;> simp
  · rename_i b j
    simp only [coordOf]
    cases kid j 2 <;> simp [Kid.coord]
  · simp [coordOf]

theorem hashOf_ne_src {v h : Name} (hh : hashOf v = some h) (b : Fin 3) (k : Fin 14) :
    h ≠ Name.src b k := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;>
    subst hh <;> intro e <;> nomatch e

/-- The exclusive kid is a source equal to its coordinate, or a value node
reading its coordinate. -/
theorem exclOf_cases {h p : Name} (hp : hashParent h = some p) :
    (∃ b k, exclOf h = Name.src b k ∧ coordOf h = Name.src b k) ∨
      hashOf (exclOf h) = some (coordOf h) := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp
  · rename_i b k t
    by_cases ht : t.val = 0
    · exact Or.inl ⟨b, k, by simp [exclOf, prev, ht], by simp [coordOf, ht]⟩
    · refine Or.inr ?_
      simp only [exclOf, coordOf, dif_neg ht]
      exact hashOf_prev b k t ht
  · exact Or.inr (hashOf_kidName _ _)
  · exact Or.inr rfl

theorem lowWord_val_compress {h p : Name} (hp : hashParent h = some p)
    (xi : Rec) : lowWord (val xi p) = lowWord (val xi (exclOf h)) := by
  rw [val_hashParent hp]
  exact (lowWord_detVal_compress hp (graph.evalRec xi)).trans (lowWord_evalRec xi _)

theorem card_filter_le_of_imp_game (p : BitVec 256 → Prop)
    [DecidablePred p] (a : BitVec 129)
    (hp : ∀ z, p z → lowWord z = a) :
    (Finset.univ.filter p).card ≤ 2 ^ 127 :=
  le_trans (Finset.card_le_card fun z hz => Finset.mem_filter.2
    ⟨Finset.mem_univ _, hp z (Finset.mem_filter.1 hz).2⟩)
    (WideForest.card_filter_lowWord_le a)

/-- Resampling `coordOf h` leaves at most 127 unconstrained answer bits in a
fixed input to hash node `h`. -/
theorem card_updHash_input_le {h p : Name}
    (hp : hashParent h = some p) (xi : Rec)
    (hs : ∀ b k, coordOf h ≠ Name.src b k) (u : BitVec p.len) :
    (Finset.univ.filter fun z : BitVec 256 =>
      val (updHash xi (coordOf h) z) p = u).card ≤ 2 ^ 127 := by
  have hv : hashOf (exclOf h) = some (coordOf h) := by
    rcases exclOf_cases hp with ⟨b, k, -, e⟩ | e
    · exact absurd e (hs b k)
    · exact e
  refine card_filter_le_of_imp_game _ (lowWord u) fun z hz => ?_
  rw [← hz, lowWord_val_compress hp, lowWord_val_value hv, updHash_snd_self]
  rfl

theorem card_updSrc_input_le {h p : Name}
    (hp : hashParent h = some p) (xi : Rec) {b : Fin 3} {k : Fin 14}
    (hs : coordOf h = Name.src b k) (u : BitVec p.len) :
    (Finset.univ.filter fun z : BitVec 129 =>
      val (updSrc xi b k z) p = u).card ≤ 1 := by
  have he : exclOf h = Name.src b k := by
    rcases exclOf_cases hp with ⟨b', k', e, e'⟩ | e
    · rw [e, ← e', hs]
    · rw [hs] at e
      exact absurd rfl (hashOf_ne_src e b k)
  rw [Finset.card_le_one]
  intro z hz z' hz'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
  have e := congrArg lowWord (hz.trans hz'.symm)
  rw [lowWord_val_compress hp, lowWord_val_compress hp, he, val_updSrc_self,
    val_updSrc_self] at e
  exact eq_of_lowWord_eq rfl e

/-! ## Closed record fibers and the initial charge -/

def ClosedAt (S : Finset Rec) (s : Name) : Prop :=
  match s with
  | .src b k => ∀ xi ∈ S, ∀ z : BitVec 129, updSrc xi b k z ∈ S
  | _ => ∀ xi ∈ S, ∀ z : BitVec 256, updHash xi s z ∈ S

theorem closedAt_src (S : Finset Rec) (b : Fin 3) (k : Fin 14) :
    ClosedAt S (Name.src b k) ↔
      ∀ xi ∈ S, ∀ z : BitVec 129, updSrc xi b k z ∈ S := by
  rfl

theorem closedAt_of_ne_src (S : Finset Rec) {s : Name}
    (hs : ∀ b k, s ≠ Name.src b k) :
    ClosedAt S s ↔
      ∀ xi ∈ S, ∀ z : BitVec 256, updHash xi s z ∈ S := by
  cases s <;> simp_all [ClosedAt]

theorem bv_cast_cast_game {n m : ℕ} (h₁ : n = m) (h₂ : m = n)
    (x : BitVec n) : (x.cast h₁).cast h₂ = x := by
  subst m
  rfl

theorem updHash_updHash (xi : Rec) (s : Name) (z : BitVec 256) :
    updHash (updHash xi s z) s (xi.2 s.fin) = xi :=
  Prod.ext rfl (funext fun v => by
    show Function.update (Function.update xi.2 s.fin z) s.fin
      (xi.2 s.fin) v = xi.2 v
    by_cases hv : v = s.fin
    · subst hv
      exact Function.update_self ..
    · exact (Function.update_of_ne hv _ _).trans
        (Function.update_of_ne hv _ _))

theorem updSrc_updSrc (xi : Rec) (b : Fin 3) (k : Fin 14) (z : BitVec 129) :
    updSrc (updSrc xi b k z) b k
      ((xi.1 (Name.src b k).fin).cast (graph_len_fin _)) = xi :=
  Prod.ext (funext fun v => by
    show Function.update
      (Function.update xi.1 (Name.src b k).fin (z.cast _))
      (Name.src b k).fin
      (((xi.1 (Name.src b k).fin).cast (graph_len_fin _)).cast
        (graph_len_fin _).symm) v = xi.1 v
    by_cases hv : v = (Name.src b k).fin
    · subst hv
      exact (Function.update_self ..).trans (bv_cast_cast_game _ _ _)
    · exact (Function.update_of_ne hv _ _).trans
        (Function.update_of_ne hv _ _)) rfl

theorem fst_updSrc_self (xi : Rec) (b : Fin 3) (k : Fin 14) (z : BitVec 129) :
    ((updSrc xi b k z).1 (Name.src b k).fin).cast (graph_len_fin _) = z := by
  rw [updSrc_fst_self]
  exact bv_cast_cast_game _ _ _

theorem sum_updHash (S : Finset Rec) (s : Name)
    (hS : ∀ xi ∈ S, ∀ z : BitVec 256, updHash xi s z ∈ S)
    (f : Rec → ℝ≥0∞) :
    ∑ xi ∈ S, f xi = ∑ xi ∈ S,
      (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
        ∑ z, f (updHash xi s z) := by
  have key : ∑ xi ∈ S, ∑ z, f (updHash xi s z) =
      ∑ xi ∈ S, ∑ _z : BitVec 256, f xi := by
    calc
      ∑ xi ∈ S, ∑ z, f (updHash xi s z) =
          ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 256)),
            f (updHash p.1 s p.2) :=
        (Finset.sum_product' S Finset.univ
          (fun xi z => f (updHash xi s z))).symm
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 256)), f p.1 := by
        refine Finset.sum_nbij'
          (fun p => (updHash p.1 s p.2, p.1.2 s.fin))
          (fun p => (updHash p.1 s p.2, p.1.2 s.fin)) ?_ ?_ ?_ ?_ ?_
        · intro p hp
          rw [Finset.mem_product] at hp ⊢
          exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
        · intro p hp
          rw [Finset.mem_product] at hp ⊢
          exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
        · intro p _
          exact Prod.ext (updHash_updHash _ _ _) (updHash_snd_self _ _ _)
        · intro p _
          exact Prod.ext (updHash_updHash _ _ _) (updHash_snd_self _ _ _)
        · intro p _
          rfl
      _ = ∑ xi ∈ S, ∑ _z : BitVec 256, f xi :=
        Finset.sum_product' S Finset.univ (fun xi _ => f xi)
  have hc0 : (Fintype.card (BitVec 256) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card (BitVec 256) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [← Finset.mul_sum, key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc,
    ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem sum_updSrc (S : Finset Rec) (b : Fin 3) (k : Fin 14)
    (hS : ∀ xi ∈ S, ∀ z : BitVec 129, updSrc xi b k z ∈ S)
    (f : Rec → ℝ≥0∞) :
    ∑ xi ∈ S, f xi = ∑ xi ∈ S,
      (Fintype.card (BitVec 129) : ℝ≥0∞)⁻¹ *
        ∑ z, f (updSrc xi b k z) := by
  have key : ∑ xi ∈ S, ∑ z, f (updSrc xi b k z) =
      ∑ xi ∈ S, ∑ _z : BitVec 129, f xi := by
    calc
      ∑ xi ∈ S, ∑ z, f (updSrc xi b k z) =
          ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 129)),
            f (updSrc p.1 b k p.2) :=
        (Finset.sum_product' S Finset.univ
          (fun xi z => f (updSrc xi b k z))).symm
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 129)), f p.1 := by
        refine Finset.sum_nbij'
          (fun p => (updSrc p.1 b k p.2,
            (p.1.1 (Name.src b k).fin).cast (graph_len_fin _)))
          (fun p => (updSrc p.1 b k p.2,
            (p.1.1 (Name.src b k).fin).cast (graph_len_fin _))) ?_ ?_ ?_ ?_ ?_
        · intro p hp
          rw [Finset.mem_product] at hp ⊢
          exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
        · intro p hp
          rw [Finset.mem_product] at hp ⊢
          exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
        · intro p _
          exact Prod.ext (updSrc_updSrc _ _ _ _) (fst_updSrc_self _ _ _ _)
        · intro p _
          exact Prod.ext (updSrc_updSrc _ _ _ _) (fst_updSrc_self _ _ _ _)
        · intro p _
          rfl
      _ = ∑ xi ∈ S, ∑ _z : BitVec 129, f xi :=
        Finset.sum_product' S Finset.univ (fun xi _ => f xi)
  have hc0 : (Fintype.card (BitVec 129) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card (BitVec 129) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [← Finset.mul_sum, key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc,
    ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem card_bitVec_ennreal_game (n : ℕ) :
    (Fintype.card (BitVec n) : ℝ≥0∞) = 2 ^ n := by simp

theorem sum_input_eq_le {h p : Name} (hp : hashParent h = some p)
    (S : Finset Rec) (hS : ClosedAt S (coordOf h))
    (u : BitVec p.len) :
    ∑ xi ∈ S, (if val xi p = u then w else 0) ≤
      ε * ∑ _xi ∈ S, w := by
  rw [Finset.mul_sum]
  by_cases hsrc : ∃ b k, coordOf h = Name.src b k
  · obtain ⟨b, k, hk⟩ := hsrc
    rw [hk, closedAt_src] at hS
    rw [sum_updSrc S b k hS
      (fun xi => if val xi p = u then w else 0)]
    refine Finset.sum_le_sum fun xi _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hle := card_updSrc_input_le hp xi hk u
    have hle' : ((Finset.univ.filter fun z : BitVec 129 =>
        val (updSrc xi b k z) p = u).card : ℝ≥0∞) ≤ 1 := by
      exact_mod_cast hle
    calc
      (Fintype.card (BitVec 129) : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun z : BitVec 129 =>
            val (updSrc xi b k z) p = u).card : ℝ≥0∞) * w)
          ≤ (Fintype.card (BitVec 129) : ℝ≥0∞)⁻¹ * (1 * w) := by
            gcongr
      _ = ε * w := by
        rw [one_mul, card_bitVec_ennreal_game, ε]
  · push Not at hsrc
    rw [closedAt_of_ne_src S hsrc] at hS
    rw [sum_updHash S (coordOf h) hS
      (fun xi => if val xi p = u then w else 0)]
    refine Finset.sum_le_sum fun xi _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hle := card_updHash_input_le hp xi hsrc u
    have hle' : ((Finset.univ.filter fun z : BitVec 256 =>
        val (updHash xi (coordOf h) z) p = u).card : ℝ≥0∞) ≤
          2 ^ 127 := by
      exact_mod_cast hle
    calc
      (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun z : BitVec 256 =>
            val (updHash xi (coordOf h) z) p = u).card : ℝ≥0∞) * w)
          ≤ (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            (2 ^ 127 * w) := by
              gcongr
      _ = ε * w := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc] using
          congrArg (fun z : ℝ≥0∞ => z * w) inv_card_bitVec_mul_two_pow

theorem pkOf_updHash (xi : Rec) {s : Name} (hs : s ≠ Name.rh)
    (z : BitVec 256) : pkOf (updHash xi s z) = pkOf xi := by
  exact congrArg lowPk (updHash_snd_ne xi s z (Ne.symm hs))

theorem pkOf_updSrc (xi : Rec) (b : Fin 3) (k : Fin 14) (z : BitVec 129) :
    pkOf (updSrc xi b k z) = pkOf xi := by
  unfold pkOf
  rw [updSrc_snd]

theorem fiberA_closedAt (pk : BitVec 128) {s : Name}
    (hs : s ≠ Name.rh) : ClosedAt (fiberA pk) s := by
  by_cases hsrc : ∃ b k, s = Name.src b k
  · obtain ⟨b, k, rfl⟩ := hsrc
    rw [closedAt_src]
    simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
    intro xi hxi z
    rw [pkOf_updSrc]
    exact hxi
  · push Not at hsrc
    rw [closedAt_of_ne_src _ hsrc]
    simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
    intro xi hxi z
    rw [pkOf_updHash _ hs]
    exact hxi

/-- The concrete pre-sign fiber satisfies the raw hidden-input charge. -/
theorem initialHitsCharge : InitialHitsCharge := by
  intro pk q
  by_cases hex : ∃ h p, hashParent h = some p ∧
      ∃ xi₀ : Rec, q = pointOf xi₀ h p
  · obtain ⟨h, p, hp, xi₀, rfl⟩ := hex
    have key : ∀ xi : Rec,
        (kc xi (pointOf xi₀ h p)).isSome ↔ val xi p = val xi₀ p := by
      intro xi
      rw [kc_isSome_iff]
      constructor
      · rintro ⟨h', p', hp', e⟩
        obtain rfl := pointOf_inj_left hp hp' e
        rw [hp] at hp'
        obtain rfl := Option.some.inj hp'
        exact (pointOf_inj_input e).symm
      · intro hv
        exact ⟨h, p, hp, by simp only [pointOf, hv]⟩
    have hcost : h.cost ≠ 0 := cost_ne_zero_of_hashParent hp
    calc
      ∑ xi ∈ fiberA pk,
          (if (kc xi (pointOf xi₀ h p)).isSome then w else 0) =
          ∑ xi ∈ fiberA pk, (if val xi p = val xi₀ p then w else 0) := by
        refine Finset.sum_congr rfl fun xi _ => ?_
        by_cases hv : val xi p = val xi₀ p <;> simp [key, hv]
      _ ≤ _ := sum_input_eq_le hp _
        (fiberA_closedAt pk (coordOf_ne_rh h hcost)) _
  · have hz : ∀ xi : Rec, ¬ (kc xi q).isSome := by
      intro xi hk
      rw [kc_isSome_iff] at hk
      obtain ⟨h, p, hp, e⟩ := hk
      exact hex ⟨h, p, hp, xi, e⟩
    have hsum : ∑ xi ∈ fiberA pk,
        (if (kc xi q).isSome then w else 0) = 0 :=
      Finset.sum_eq_zero fun xi _ => if_neg (hz xi)
    exact hsum.le.trans _root_.zero_le

/-! ## Locality of record coordinates -/

/-- The independent record coordinate underlying a 129-bit value: the hash
node it reads, or the source itself. -/
def valueCoord (n : Name) : Name := (hashOf n).getD n

theorem valueCoord_of_hashOf {v h : Name} (hh : hashOf v = some h) :
    valueCoord v = h := by
  simp [valueCoord, hh]

theorem valueCoord_of_hashOf_none {n : Name} (hn : hashOf n = none) :
    valueCoord n = n := by
  simp [valueCoord, hn]

/-- Record coordinates read by the honest value at a node. -/
def deps (n : Name) : Finset Name :=
  if ∃ h, hashParent h = some n then (parents n).image valueCoord
  else {valueCoord n}

theorem evalRec_fin_congr {xi xi' : Rec} {a : Name}
    (h : val xi a = val xi' a) :
    graph.evalRec xi a.fin = graph.evalRec xi' a.fin := by
  unfold val at h
  simpa using congrArg (BitVec.cast (graph_len_fin a).symm) h

theorem val_hash_congr {xi xi' : Rec} {h p : Name} (hp : hashParent h = some p)
    (e : xi.2 h.fin = xi'.2 h.fin) : val xi h = val xi' h := by
  unfold val
  rw [evalRec_apply_fin, evalRec_apply_fin]
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    simp only [kindOf, NodeKind.value, e]

theorem val_src_congr {xi xi' : Rec} {b : Fin 3} {k : Fin 14}
    (e : xi.1 (Name.src b k).fin = xi'.1 (Name.src b k).fin) :
    val xi (Name.src b k) = val xi' (Name.src b k) := by
  rw [val_src, val_src, e]

/-- A 129-bit value depends only on its record coordinate. -/
theorem val_input_congr {xi xi' : Rec} {e : Name} (he : e.len = 129)
    (hsrc : ∀ b k, e = Name.src b k → xi.1 e.fin = xi'.1 e.fin)
    (hval : ∀ h, hashOf e = some h → xi.2 h.fin = xi'.2 h.fin) :
    val xi e = val xi' e := by
  rcases len_eq_129_cases he with ⟨b, k, rfl⟩ | ⟨h, hh⟩
  · exact val_src_congr (hsrc b k rfl)
  · apply eq_of_lowWord_eq he
    rw [lowWord_val_value hh, lowWord_val_value hh, hval h hh]

/-- A compression input depends only on the values of its inputs. -/
theorem val_compress_congr {xi xi' : Rec} {h p : Name}
    (hp : hashParent h = some p)
    (H : ∀ e ∈ parents p, val xi e = val xi' e) : val xi p = val xi' p := by
  rw [val_hashParent hp, val_hashParent hp]
  apply detVal_local
  intro v hv
  rw [Name.parentFins, Finset.mem_map] at hv
  obtain ⟨e, he, rfl⟩ := hv
  exact evalRec_fin_congr (H e he)

theorem not_mem_deps_compress {s p e : Name} (hc : ∃ h, hashParent h = some p)
    (hs : s ∉ deps p) (he : e ∈ parents p) : s ≠ valueCoord e := by
  intro hse
  apply hs
  rw [deps, if_pos hc, Finset.mem_image]
  exact ⟨e, he, hse.symm⟩

theorem not_mem_deps_other {s n : Name} (hc : ¬ ∃ h, hashParent h = some n)
    (hs : s ∉ deps n) : s ≠ valueCoord n := by
  intro hse
  apply hs
  rw [deps, if_neg hc, hse, Finset.mem_singleton]

theorem val_updHash_of_not_mem_deps (xi : Rec) (s : Name)
    (z : BitVec 256) (n : Name) (h : s ∉ deps n) :
    val (updHash xi s z) n = val xi n := by
  have hin : ∀ e : Name, e.len = 129 → s ≠ valueCoord e →
      val (updHash xi s z) e = val xi e := fun e he hse =>
    val_input_congr he (fun _ _ _ => rfl) fun h hh =>
      updHash_snd_ne xi s z (fun e' => hse (by rw [valueCoord_of_hashOf hh, e']))
  rcases role_cases n with ⟨b, k, rfl⟩ | ⟨p, hp⟩ | ⟨h', hp⟩ | ⟨h', hh⟩
  · exact val_src_congr rfl
  · have hc : ¬ ∃ h, hashParent h = some n := fun ⟨h₀, h₀p⟩ => by
      rw [hashParent_hashParent h₀p] at hp
      exact absurd hp (by simp)
    have hsn := not_mem_deps_other hc h
    rw [valueCoord_of_hashOf_none (hashOf_of_hashParent hp)] at hsn
    exact val_hash_congr hp (updHash_snd_ne xi s z (Ne.symm hsn))
  · exact val_compress_congr hp fun e he =>
      hin e (len_of_mem_parents_compress hp he)
        (not_mem_deps_compress ⟨h', hp⟩ h he)
  · have hc : ¬ ∃ h, hashParent h = some n := fun ⟨h₀, h₀p⟩ => by
      rw [hashOf_hashParent h₀p] at hh
      exact absurd hh (by simp)
    exact hin n (len_value_of_hashOf hh) (not_mem_deps_other hc h)

theorem val_updSrc_of_not_mem_deps (xi : Rec) (b : Fin 3) (k : Fin 14)
    (z : BitVec 129) (n : Name) (h : Name.src b k ∉ deps n) :
    val (updSrc xi b k z) n = val xi n := by
  have hin : ∀ e : Name, e.len = 129 → Name.src b k ≠ valueCoord e →
      val (updSrc xi b k z) e = val xi e := fun e he hse =>
    val_input_congr he
      (fun b' k' e' => by
        subst e'
        rw [valueCoord_of_hashOf_none rfl] at hse
        exact Function.update_of_ne (fun e => hse (Name.fin_injective e).symm) _ _)
      fun _ _ => rfl
  rcases role_cases n with ⟨b', k', rfl⟩ | ⟨p, hp⟩ | ⟨h', hp⟩ | ⟨h', hh⟩
  · have hc : ¬ ∃ h, hashParent h = some (Name.src b' k') := fun ⟨h₀, h₀p⟩ =>
      hashParent_ne_src h₀p b' k' rfl
    exact hin _ rfl (not_mem_deps_other hc h)
  · exact val_hash_congr hp rfl
  · exact val_compress_congr hp fun e he =>
      hin e (len_of_mem_parents_compress hp he)
        (not_mem_deps_compress ⟨h', hp⟩ h he)
  · have hc : ¬ ∃ h, hashParent h = some n := fun ⟨h₀, h₀p⟩ => by
      rw [hashOf_hashParent h₀p] at hh
      exact absurd hh (by simp)
    exact hin n (len_value_of_hashOf hh) (not_mem_deps_other hc h)

/-! ## Hidden-coordinate locality after signing -/

def HiddenCoord (A : Finset Name) (s : Name) : Prop :=
  ¬ Evaluated A s ∧ s ∉ A ∧
    ∀ a ∈ A, hashOf a ≠ some s

theorem not_mem_deps_of_hiddenCoord {A : Finset Name} (hA : IsCut A)
    {s n : Name} (hs : HiddenCoord A s)
    (hn : Evaluated A n ∨ n ∈ A) : s ∉ deps n := by
  obtain ⟨hsE, hsA, hsH⟩ := hs
  -- `s` read at the value level of a visited 129-bit node `e` forces `s` visible.
  have hval : ∀ e, (Evaluated A e ∨ e ∈ A) → s ≠ valueCoord e := by
    intro e he hse
    cases hh : hashOf e with
    | none =>
        rw [valueCoord_of_hashOf_none hh] at hse
        subst hse
        rcases he with he | he
        · exact hsE he
        · exact hsA he
    | some h =>
        rw [valueCoord_of_hashOf hh] at hse
        subst hse
        rcases he with he | he
        · exact hsE ⟨(visited_hash_iff hh).2 he, hsA⟩
        · exact hsH e he hh
  intro hd
  unfold deps at hd
  split_ifs at hd with hc
  · obtain ⟨h, hp⟩ := hc
    rw [Finset.mem_image] at hd
    obtain ⟨e, he, rfl⟩ := hd
    rcases hn with hn | hn
    · exact hval e (evaluated_or_mem_of_mem_parents hn he) rfl
    · exact not_mem_of_cut_len_ne hA (len_hashParent_ne_129 hp) hn
  · rw [Finset.mem_singleton] at hd
    exact hval n hn hd

theorem hiddenCoord_ne_rh {A : Finset Name} {s : Name}
    (hs : HiddenCoord A s) : s ≠ Name.rh := by
  rintro rfl
  exact hs.1 ⟨Graph.Visited.root, hs.2.1⟩

theorem encode_congr_game (G : Graph) (B : Finset (Fin G.size))
    {x x' : G.Assignment} (h : ∀ v ∈ B, x v = x' v) :
    G.encode B x = G.encode B x' := by
  unfold Graph.encode
  refine List.flatMap_congr fun v hv => ?_
  rw [List.mem_filter, decide_eq_true_iff] at hv
  rw [h v hv.2]

theorem revealed_updHash {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {s : Name} (hs : HiddenCoord A s) (z : BitVec 256) :
    revealed A (updHash xi s z) = revealed A xi := by
  unfold revealed
  apply encode_congr_game
  intro v hv
  obtain ⟨a, rfl⟩ : ∃ a : Name, a.fin = v :=
    ⟨Name.ofFin v, Name.fin_ofFin v⟩
  have haA : a ∈ A := (mem_fins_embedding A a).1 hv
  exact evalRec_fin_congr
    (val_updHash_of_not_mem_deps xi s z a
      (not_mem_deps_of_hiddenCoord hA hs (Or.inr haA)))

theorem revealed_updSrc {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {b : Fin 3} {k : Fin 14} (hs : HiddenCoord A (Name.src b k))
    (z : BitVec 129) : revealed A (updSrc xi b k z) = revealed A xi := by
  unfold revealed
  apply encode_congr_game
  intro v hv
  obtain ⟨a, rfl⟩ : ∃ a : Name, a.fin = v :=
    ⟨Name.ofFin v, Name.fin_ofFin v⟩
  have haA : a ∈ A := (mem_fins_embedding A a).1 hv
  exact evalRec_fin_congr
    (val_updSrc_of_not_mem_deps xi b k z a
      (not_mem_deps_of_hiddenCoord hA hs (Or.inr haA)))

theorem pointOf_updHash {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {s : Name} (hs : HiddenCoord A s) (z : BitVec 256)
    {h p : Name} (hp : hashParent h = some p) (he : Evaluated A h) :
    pointOf (updHash xi s z) h p = pointOf xi h p := by
  unfold pointOf
  rw [val_updHash_of_not_mem_deps _ _ _ _
    (not_mem_deps_of_hiddenCoord hA hs
      (evaluated_or_mem_of_mem_parents he (mem_parents_hashParent hp)))]

theorem pointOf_updSrc {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {b : Fin 3} {k : Fin 14} (hs : HiddenCoord A (Name.src b k))
    (z : BitVec 129) {h p : Name} (hp : hashParent h = some p)
    (he : Evaluated A h) :
    pointOf (updSrc xi b k z) h p = pointOf xi h p := by
  unfold pointOf
  rw [val_updSrc_of_not_mem_deps _ _ _ _ _
    (not_mem_deps_of_hiddenCoord hA hs
      (evaluated_or_mem_of_mem_parents he (mem_parents_hashParent hp)))]

theorem kc_pointOf (xi : Rec) {h p : Name}
    (hp : hashParent h = some p) :
    kc xi (pointOf xi h p) = some (xi.2 h.fin) :=
  (kc_apply_iff xi _ _).2 ⟨h, p, hp, rfl, rfl⟩

theorem fExp_updHash {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {s : Name} (hs : HiddenCoord A s) (z : BitVec 256) :
    fExp (some A) (updHash xi s z) = fExp (some A) xi := by
  funext q
  have hpt : ∀ h p, hashParent h = some p → Exposed (some A) h →
      pointOf (updHash xi s z) h p = pointOf xi h p :=
    fun h p hp he => pointOf_updHash hA xi hs z hp
      ((exposed_some_iff_evaluated A h).1 he)
  have hcond : (∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
      q = pointOf (updHash xi s z) h p) ↔
      ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
        q = pointOf xi h p := by
    constructor
    · rintro ⟨h, p, hp, he, hq⟩
      exact ⟨h, p, hp, he, hq.trans (hpt h p hp he)⟩
    · rintro ⟨h, p, hp, he, hq⟩
      exact ⟨h, p, hp, he, hq.trans (hpt h p hp he).symm⟩
  simp only [fExp]
  by_cases hq : ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
      q = pointOf xi h p
  · rw [if_pos (hcond.2 hq), if_pos hq]
    obtain ⟨h, p, hp, he, rfl⟩ := hq
    have hne : h ≠ s := fun e => hs.1
      (e ▸ (exposed_some_iff_evaluated A h).1 he)
    rw [kc_pointOf xi hp, ← hpt h p hp he, kc_pointOf _ hp,
      updHash_snd_ne _ _ _ hne]
  · rw [if_neg (fun h' => hq (hcond.1 h')), if_neg hq]

theorem fExp_updSrc {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {b : Fin 3} {k : Fin 14} (hs : HiddenCoord A (Name.src b k))
    (z : BitVec 129) :
    fExp (some A) (updSrc xi b k z) = fExp (some A) xi := by
  funext q
  have hpt : ∀ h p, hashParent h = some p → Exposed (some A) h →
      pointOf (updSrc xi b k z) h p = pointOf xi h p :=
    fun h p hp he => pointOf_updSrc hA xi hs z hp
      ((exposed_some_iff_evaluated A h).1 he)
  have hcond : (∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
      q = pointOf (updSrc xi b k z) h p) ↔
      ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
        q = pointOf xi h p := by
    constructor
    · rintro ⟨h, p, hp, he, hq⟩
      exact ⟨h, p, hp, he, hq.trans (hpt h p hp he)⟩
    · rintro ⟨h, p, hp, he, hq⟩
      exact ⟨h, p, hp, he, hq.trans (hpt h p hp he).symm⟩
  simp only [fExp]
  by_cases hq : ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
      q = pointOf xi h p
  · rw [if_pos (hcond.2 hq), if_pos hq]
    obtain ⟨h, p, hp, he, rfl⟩ := hq
    rw [kc_pointOf xi hp, ← hpt h p hp he, kc_pointOf _ hp, updSrc_snd]
  · rw [if_neg (fun h' => hq (hcond.1 h')), if_neg hq]

theorem dataOf_updHash {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {s : Name} (hs : HiddenCoord A s) (z : BitVec 256) :
    dataOf A (updHash xi s z) = dataOf A xi := by
  simp only [dataOf, pkOf_updHash _ (hiddenCoord_ne_rh hs),
    revealed_updHash hA _ hs, fExp_updHash hA _ hs]

theorem dataOf_updSrc {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {b : Fin 3} {k : Fin 14} (hs : HiddenCoord A (Name.src b k))
    (z : BitVec 129) : dataOf A (updSrc xi b k z) = dataOf A xi := by
  simp only [dataOf, pkOf_updSrc, revealed_updSrc hA _ hs,
    fExp_updSrc hA _ hs]

theorem fiberB_closedAt {A : Finset Name} (hA : IsCut A) (dt : Data)
    {s : Name} (hs : HiddenCoord A s) : ClosedAt (fiberB A dt) s := by
  by_cases hsrc : ∃ b k, s = Name.src b k
  · obtain ⟨b, k, rfl⟩ := hsrc
    rw [closedAt_src]
    simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and]
    intro xi hxi z
    rw [dataOf_updSrc hA _ hs]
    exact hxi
  · push Not at hsrc
    rw [closedAt_of_ne_src _ hsrc]
    simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and]
    intro xi hxi z
    rw [dataOf_updHash hA _ hs]
    exact hxi

/-- If a hash node is not reconstructed, its exclusive kid is not visited:
that kid is read only by the input of the hash node. -/
theorem not_visited_exclOf {A : Finset Name} {h p : Name}
    (hp : hashParent h = some p) (hh : ¬ Evaluated A h) :
    ¬ graph.Visited (fins A) (exclOf h).fin := by
  intro hv
  have hlen : (exclOf h).len = 129 :=
    len_of_mem_parents_compress hp (exclOf_mem hp)
  rcases visited_cases hv with e | ⟨m, hm, hmE⟩
  · rw [e] at hlen
    simp [Name.len] at hlen
  · rw [consumer_of_exclOf hp hm] at hmE
    exact hh ((visited_compress_iff hp).1 hmE.1)

/-- The coordinate behind the exclusive kid of a hidden hash node is hidden. -/
theorem coordOf_hiddenCoord {A : Finset Name} (hA : IsCut A)
    {h p : Name} (hp : hashParent h = some p)
    (hh : ¬ Evaluated A h) : HiddenCoord A (coordOf h) := by
  have hnv := not_visited_exclOf hp hh
  have hnA : exclOf h ∉ A := fun hm => hnv (hA.visited_of_mem hm)
  rcases exclOf_cases hp with ⟨b, k, he, hc⟩ | hv
  · rw [hc]
    rw [he] at hnv hnA
    exact ⟨fun hE => hnv hE.1, hnA, fun a _ ha => hashOf_ne_src ha b k rfl⟩
  · refine ⟨fun hE => hnv ((visited_hash_iff hv).1 hE.1).1, fun hm => ?_,
      fun a ha hac => hnA ?_⟩
    · have := hA.values _ hm
      rw [len_of_hashOf hv] at this
      omega
    · rwa [← hashOf_injective hac hv]

/-- The concrete post-sign public-data fiber satisfies the raw hidden-input
charge used by `authPotential_charge`. -/
theorem signedHitsCharge : SignedHitsCharge := by
  intro A hA dt q
  by_cases hex : ∃ h p, hashParent h = some p ∧ ¬ Evaluated A h ∧
      ∃ xi₀ : Rec, q = pointOf xi₀ h p
  · obtain ⟨h, p, hp, hh, xi₀, rfl⟩ := hex
    have key : ∀ xi : Rec,
        (fHid (some A) xi (pointOf xi₀ h p)).isSome ↔
          val xi p = val xi₀ p := by
      intro xi
      rw [fHid_isSome_some_iff]
      constructor
      · rintro ⟨h', p', hp', _, e⟩
        obtain rfl := pointOf_inj_left hp hp' e
        rw [hp] at hp'
        obtain rfl := Option.some.inj hp'
        exact (pointOf_inj_input e).symm
      · intro hv
        exact ⟨h, p, hp, hh, by simp only [pointOf, hv]⟩
    calc
      ∑ xi ∈ fiberB A dt,
          (if (fHid (some A) xi (pointOf xi₀ h p)).isSome then w else 0) =
          ∑ xi ∈ fiberB A dt,
            (if val xi p = val xi₀ p then w else 0) := by
        refine Finset.sum_congr rfl fun xi _ => ?_
        by_cases hv : val xi p = val xi₀ p <;> simp [key, hv]
      _ ≤ _ := sum_input_eq_le hp _
        (fiberB_closedAt hA dt (coordOf_hiddenCoord hA hp hh)) _
  · have hz : ∀ xi : Rec, ¬ (fHid (some A) xi q).isSome := by
      intro xi hk
      rw [fHid_isSome_some_iff] at hk
      obtain ⟨h, p, hp, hh, e⟩ := hk
      exact hex ⟨h, p, hp, hh, xi, e⟩
    have hsum : ∑ xi ∈ fiberB A dt,
        (if (fHid (some A) xi q).isSome then w else 0) = 0 :=
      Finset.sum_eq_zero fun xi _ => if_neg (hz xi)
    exact hsum.le.trans _root_.zero_le

theorem hits_charge_A' (pk : BitVec 128) {T : Finset Rec}
    (hT : T ⊆ fiberA pk) (q : Query) :
    ∑ xi ∈ T, w * ind ((kc xi q).isSome) ≤ ε * sumW (fiberA pk) :=
  hits_charge_A'_of initialHitsCharge pk hT q

theorem authPotential_charge {A : Finset Name} (hA : IsCut A) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB A dt)
    (c : Cache) (q : Query) (hq : c q = none) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      authPotential T (some A) (c.cacheQuery q u)) ≤
      authPotential T (some A) c +
        authRate * sumW (fiberB A dt) * queryCost (.inr q) :=
  authPotential_charge_of signedHitsCharge hA dt hT c q hq

/-! ## Same-class payload authentication -/

theorem encode_congr (G : Graph) (A : Finset (Fin G.size))
    {x x' : G.Assignment} (h : ∀ v ∈ A, x v = x' v) :
    G.encode A x = G.encode A x' := by
  unfold Graph.encode
  refine List.flatMap_congr fun v hv => ?_
  rw [List.mem_filter, decide_eq_true_iff] at hv
  rw [h v hv.2]

/-- A forged payload for the signed class differs at a disclosed value, and
that difference reaches a spurious graph binding. -/
theorem events_same {A : Finset Name} (hA : IsCut A)
    {xi : Rec} {d : Cache} {x' : List Bool} {y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A) (graph.decode (fins A) x') y)
    (hacc : lowPk (yv y Name.rh) = pkOf xi)
    (hlen : x'.length = graph.revealBits (fins A))
    (hne : x' ≠ graph.encode (fins A) (graph.evalRec xi)) : Spr d xi := by
  have hex : ∃ a ∈ A,
      graph.decode (fins A) x' a.fin ≠ graph.evalRec xi a.fin := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [← graph.encode_decode (fins A) x' hlen]
    apply encode_congr
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    exact hcon a ha
  obtain ⟨a, ha, hne'⟩ := hex
  rcases descent_mem hA hy hacc ha with hs | heq
  · exact hs
  · exfalso
    apply hne'
    rw [yv_mem hy ha] at heq
    unfold val at heq
    exact cast_injective _ heq

/-! ## Accepted-run decomposition with one explicit cross-cut seam -/

/-- The graph-specific statement still needed for distinct schedule classes.
It is separated so the accepted-game endgame does not depend on how the cut
comparison proof is eventually organized. -/
def CrossCutAuthentication : Prop :=
  ∀ (xi : Rec) (signedClass i : Fin M) (d : Cache)
    (given y : graph.Assignment),
    i ≠ signedClass →
    graph.ReconEqs d (fins (setsName i)) given y →
    lowPk (yv y Name.rh) = pkOf xi →
      Spr d xi ∨
        Cache.Hits d (fHid (some (setsName signedClass)) xi)

/-- Given the cross-cut authentication lemma, every accepted verification is
honest for the signed class or reaches one of the two authentication events. -/
theorem accepted_class_cases (hcross : CrossCutAuthentication)
    (xi : Rec) (signedClass : Fin M) (m : Message)
    (sigma : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (scheme.verify (pkOf xi) m sigma) c)) :
    ∃ answer, d (encQuery (m, sigma.1)) = some answer ∧
      ∃ i : Fin M, LongChain91Schedule.decode answer = some i ∧
        ((i = signedClass ∧
            sigma.2 = graph.encode (fins (setsName signedClass))
              (graph.evalRec xi)) ∨
          Spr d xi ∨
          Cache.Hits d (fHid (some (setsName signedClass)) xi)) := by
  obtain ⟨_, hh⟩ :=
    WeightedScheme.verify_support scheme (pkOf xi) m sigma c (true, d) h
  obtain ⟨answer, ha, i, hi, hlen, y, hy, hpk⟩ := hh rfl
  refine ⟨answer, ha, i, hi, ?_⟩
  have hacc := accepted_lowPk xi y hpk
  by_cases hic : i = signedClass
  · subst i
    by_cases hpayload : sigma.2 =
        graph.encode (fins (setsName signedClass)) (graph.evalRec xi)
    · exact Or.inl ⟨rfl, hpayload⟩
    · exact Or.inr (Or.inl
        (events_same (isCut_of_mem_family (setsName_mem signedClass))
          hy hacc hlen hpayload))
  · exact Or.inr (hcross xi signedClass i d _ y hic hy hacc)

/-- Public name for the cached-row alternate-input event.  This is
definitionally the predicate used by its replay bound. -/
abbrev AlternateClass (c : Cache) (signedInput : EncInput)
    (i : Fin M) : Prop :=
  LongChain91CachedRow.alternateClass c signedInput i

end OptimalOTS.WeightedConstruction.LongChain91
