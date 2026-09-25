import Submissions.UpperLeanIsa.FusionCoherence
import Submissions.UpperLeanIsa.FusionExposure
import Submissions.UpperLeanIsa.KeygenBridge

namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical
noncomputable section
variable {P : Params}

theorem avg_hash (a : Loc P) (x : Tbl P → BitVec 896) (c : Tbl P → Cache)
    (K : Tbl P → BitVec hashBits × Cache → ℝ≥0∞)
    (hfresh : ∀ y, c y ⟨896, x y⟩ = none)
    (hx : ∀ y u, x (Function.update y a u) = x y)
    (hc : ∀ y u, c (Function.update y a u) = c y)
    (hK : ∀ y u p, K (Function.update y a u) p = K y p) :
    ∑ y : Tbl P, (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ * E (run (hash (x y)) (c y)) (K y) =
      ∑ y : Tbl P, (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ *
        K y (y a, (c y).cacheQuery ⟨896, x y⟩ (y a)) := by
  have key := sum_avg_update (R := fun _ : Loc P => BitVec hashBits) a
    (fun u y => K y (u, (c y).cacheQuery ⟨896, x y⟩ u))
    (fun u u' y => by rw [hK, hc, hx y u'])
  refine Eq.trans ?_ key
  have h1 : ∀ y : Tbl P, E (run (hash (x y)) (c y)) (K y) =
      ∑ u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        K y (u, (c y).cacheQuery ⟨896, x y⟩ u) := by
    intro y
    rw [run_hash_fresh _ _ (hfresh y), E_bind, E_uniform]
    simp only [E_pure]
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [mul_left_comm]

def progUpd (ξ : Record P) (S : Loc P → Prop) (c : Cache) : Cache :=
  fun q => if ∃ a, S a ∧ ξ.query a = q then ξ.cache q else c q

theorem progUpd_apply (ξ : Record P) (S : Loc P → Prop) (c : Cache) (q : Query) :
    progUpd ξ S c q = if ∃ a, S a ∧ ξ.query a = q then ξ.cache q else c q :=
  rfl

theorem progUpd_apply_neg {ξ : Record P} {S : Loc P → Prop} {c : Cache}
    {q : Query} (h : ¬ ∃ a, S a ∧ ξ.query a = q) : progUpd ξ S c q = c q := by
  rw [progUpd_apply, if_neg h]

theorem progUpd_of_false (ξ : Record P) (S : Loc P → Prop) (c : Cache)
    (h : ∀ b, ¬ S b) : progUpd ξ S c = c := by
  funext q
  have hn : ¬ ∃ a, S a ∧ ξ.query a = q := fun ⟨a, ha, _⟩ => h a ha
  rw [progUpd_apply, if_neg hn]

theorem progUpd_congr {ξ : Record P} {S S' : Loc P → Prop} {c : Cache}
    (h : ∀ b, S b ↔ S' b) : progUpd ξ S c = progUpd ξ S' c := by
  have hSS : S = S' := funext fun b => propext (h b)
  rw [hSS]

theorem progUpd_cacheQuery (hP : P.Hyp) (ξ : Record P) (S : Loc P → Prop) (c : Cache)
    (a : Loc P) :
    progUpd ξ S (c.cacheQuery (ξ.query a) (ξ.2 a)) = progUpd ξ (fun b => S b ∨ b = a) c := by
  funext q
  rw [progUpd_apply, progUpd_apply]
  by_cases hq : ξ.query a = q
  · subst hq
    have h1 : ∃ b, (S b ∨ b = a) ∧ ξ.query b = ξ.query a := ⟨a, Or.inr rfl, rfl⟩
    rw [if_pos h1]
    by_cases h : ∃ b, S b ∧ ξ.query b = ξ.query a
    · rw [if_pos h]
    · rw [if_neg h, QueryCache.cacheQuery_self]
      exact (ξ.cache_query hP a).symm
  · by_cases h : ∃ b, S b ∧ ξ.query b = q
    · have h1 : ∃ b, (S b ∨ b = a) ∧ ξ.query b = q := by
        obtain ⟨b, hb, hbq⟩ := h
        exact ⟨b, Or.inl hb, hbq⟩
      rw [if_pos h, if_pos h1]
    · have h1 : ¬ ∃ b, (S b ∨ b = a) ∧ ξ.query b = q := by
        rintro ⟨b, hb | rfl, hbq⟩
        · exact h ⟨b, hb, hbq⟩
        · exact hq hbq
      rw [if_neg h, if_neg h1, QueryCache.cacheQuery_of_ne _ _ (Ne.symm hq)]

theorem progUpd_progUpd (ξ : Record P) (S T : Loc P → Prop) (c : Cache) :
    progUpd ξ S (progUpd ξ T c) = progUpd ξ (fun b => S b ∨ T b) c := by
  funext q
  rw [progUpd_apply, progUpd_apply, progUpd_apply]
  by_cases hS : ∃ b, S b ∧ ξ.query b = q
  · have h1 : ∃ b, (S b ∨ T b) ∧ ξ.query b = q := by
      obtain ⟨b, hb, hbq⟩ := hS
      exact ⟨b, Or.inl hb, hbq⟩
    rw [if_pos hS, if_pos h1]
  · by_cases hT : ∃ b, T b ∧ ξ.query b = q
    · have h1 : ∃ b, (S b ∨ T b) ∧ ξ.query b = q := by
        obtain ⟨b, hb, hbq⟩ := hT
        exact ⟨b, Or.inr hb, hbq⟩
      rw [if_neg hS, if_pos hT, if_pos h1]
    · have h1 : ¬ ∃ b, (S b ∨ T b) ∧ ξ.query b = q := by
        rintro ⟨b, hb | hb, hbq⟩
        · exact hS ⟨b, hb, hbq⟩
        · exact hT ⟨b, hb, hbq⟩
      rw [if_neg hS, if_neg hT, if_neg h1]

theorem progUpd_true_empty (hP : P.Hyp) (ξ : Record P) :
    progUpd ξ (fun _ => True) ∅ = ξ.cache := by
  funext q
  rw [progUpd_apply]
  by_cases h : ∃ a, True ∧ ξ.query a = q
  · rw [if_pos h]
  · rw [if_neg h, QueryCache.empty_apply]
    cases hc : ξ.cache q with
    | none => rfl
    | some v =>
      obtain ⟨a, ha, -⟩ := (ξ.cache_some_iff hP q v).1 hc
      exact (h ⟨a, trivial, ha⟩).elim

theorem progUpd_update (hP : P.Hyp) (sk : Fin numChains → Word) (y : Tbl P) (b : Loc P)
    (u : BitVec hashBits) (S : Loc P → Prop) (c : Cache)
    (hS : ∀ b', S b' → b' ≠ b ∧
      Record.query (sk, Function.update y b u) b' = Record.query (sk, y) b') :
    progUpd (sk, Function.update y b u) S c = progUpd (sk, y) S c := by
  funext q
  rw [progUpd_apply, progUpd_apply]
  have hiff : (∃ b', S b' ∧ Record.query (sk, Function.update y b u) b' = q) ↔
      (∃ b', S b' ∧ Record.query (sk, y) b' = q) :=
    ⟨fun ⟨b', hb', hq⟩ => ⟨b', hb', (hS b' hb').2.symm.trans hq⟩,
      fun ⟨b', hb', hq⟩ => ⟨b', hb', (hS b' hb').2.trans hq⟩⟩
  by_cases h : ∃ b', S b' ∧ Record.query (sk, y) b' = q
  · rw [if_pos (hiff.2 h), if_pos h]
    obtain ⟨b', hb', rfl⟩ := h
    have h1 : Record.cache (sk, Function.update y b u) (Record.query (sk, y) b') =
        some (y b') := by
      rw [← (hS b' hb').2, Record.cache_query hP]
      exact congrArg some (Function.update_of_ne (hS b' hb').1 u y)
    have h2 : Record.cache (sk, y) (Record.query (sk, y) b') = some (y b') :=
      Record.cache_query hP (sk, y) b'
    rw [h1, h2]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]


/-- Future answers are erased before running a suffix of the DAG. -/
def erase (y : Tbl P) (l : List (Loc P)) : Tbl P := fun a => if a ∈ l then 0 else y a

theorem erase_nil (y : Tbl P) : erase y [] = y := by funext a; simp [erase]

theorem erase_update_mem (y : Tbl P) (l : List (Loc P)) (a : Loc P) (ha : a ∈ l)
    (v : BitVec hashBits) : erase (Function.update y a v) l = erase y l := by
  funext b
  by_cases hb : b ∈ l
  · simp only [erase,if_pos hb]
  · have hba : b ≠ a := by intro h; subst b; exact hb ha
    simp only [erase,if_neg hb,Function.update_of_ne hba]

theorem update_erase_cons (y : Tbl P) (a : Loc P) (l : List (Loc P)) (ha : a ∉ l) :
    Function.update (erase y (a::l)) a (y a) = erase y l := by
  funext b
  by_cases hb : b = a
  · subst b
    simp only [Function.update_self,erase,if_neg ha]
  · rw [Function.update_of_ne hb]
    simp [erase,hb]

theorem input_erase (seeds : Fin 42 → Word) (y : Tbl P) (l : List (Loc P)) (a : Loc P)
    (h : ∀ b ∈ l, ¬ Earlier b a) : Record.input (seeds,erase y l) a = Record.input (seeds,y) a := by
  apply Record.input_agree (seeds,erase y l) (seeds,y) a rfl
  intro b hb
  have hbl : b ∉ l := fun hmem => h b hmem hb
  exact if_neg hbl

/-- No query decoded as a remaining location is already in the cache. -/
def FreshLocs (P : Params) (l : List (Loc P)) (c : Cache) : Prop :=
  ∀ q a, queryLocation P q = some a → a ∈ l → c q = none

theorem freshLocs_hash (hP : P.Hyp) (seeds : Fin 42 → Word) (y : Tbl P)
    (l : List (Loc P)) (c : Cache) (hc : FreshLocs P l c) (a : Loc P) (ha : a ∈ l) :
    c ⟨896,Record.input (seeds,y) a⟩ = none := hc _ a (queryLocation_query hP (seeds,y) a) ha

theorem freshLocs_cacheQuery (hP : P.Hyp) (ξ : Record P) (a : Loc P) (l : List (Loc P))
    (ha : a ∉ l) (c : Cache) (hc : FreshLocs P (a::l) c) :
    FreshLocs P l (c.cacheQuery (ξ.query a) (ξ.2 a)) := by
  intro q b hb hbl
  have hqa : q ≠ ξ.query a := by
    intro he
    rw [he,queryLocation_query hP] at hb
    have hab := Option.some.inj hb
    exact ha (hab ▸ hbl)
  rw [QueryCache.cacheQuery_of_ne _ _ hqa]
  exact hc q b hb (by simp [hbl])

/-- Averaging fresh answers along the ordered DAG produces a uniform full record. -/
theorem E_evalLocations_avg (hP : P.Hyp) (seeds : Fin 42 → Word) :
    ∀ (l : List (Loc P)) (hl : l.Pairwise Earlier) (c : Tbl P → Cache),
      (∀ y, FreshLocs P l (c y)) →
      (∀ y a, a ∈ l → ∀ v, c (Function.update y a v) = c y) →
      ∀ F : Tbl P × Cache → ℝ≥0∞,
      ∑ y : Tbl P, (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ *
        E (run (P.evalLocations seeds l (erase y l)) (c y)) F =
      ∑ y : Tbl P, (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ *
        F (y,progUpd (seeds,y) (fun a => a ∈ l) (c y)) := by
  intro l
  induction l with
  | nil =>
    intro _ c _ _ F
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [erase_nil,Params.evalLocations,run_pure,E_pure,
      progUpd_of_false (seeds,y) (fun a => a ∈ ([] : List (Loc P))) (c y) (by simp)]
  | cons a l ih =>
    intro hl c hfr hu F
    obtain ⟨hbefore,htail⟩ := List.pairwise_cons.mp hl
    have hna : a ∉ l := by
      intro ha
      exact earlier_irrefl a (hbefore a ha)
    have hlater : ∀ b ∈ l, ¬ Earlier b a := fun b hb => earlier_asymm a b (hbefore b hb)
    have hlater' : ∀ b ∈ a::l, ¬ Earlier b a := by
      intro b hb
      rcases List.mem_cons.mp hb with he | hb
      · subst b
        exact earlier_irrefl a
      · exact hlater b hb
    let ch : Tbl P → Cache := fun y => (c y).cacheQuery (Record.query (seeds,y) a) (y a)
    have hfr' : ∀ y, FreshLocs P l (ch y) := fun y =>
      freshLocs_cacheQuery hP (seeds,y) a l hna (c y) (hfr y)
    have hu' : ∀ y b, b ∈ l → ∀ v, ch (Function.update y b v) = ch y := by
      intro y b hb v
      have hba : a ≠ b := by intro he; subst b; exact hna hb
      have hq : Record.query (seeds,Function.update y b v) a = Record.query (seeds,y) a :=
        congrArg (fun x => (⟨896,x⟩ : Query)) (Record.input_update seeds y a b v (hlater b hb))
      dsimp only [ch]
      rw [hu y b (by simp [hb]) v,hq,Function.update_of_ne hba]
    let K : Tbl P → BitVec hashBits × Cache → ℝ≥0∞ := fun y p =>
      E (run (P.evalLocations seeds l (Function.update (erase y (a::l)) a p.1)) p.2) F
    have hstep (y : Tbl P) :
        E (run (P.evalLocations seeds (a::l) (erase y (a::l))) (c y)) F =
        E (run (hash (Record.input (seeds,y) a)) (c y)) (K y) := by
      rw [Params.evalLocations,run_bind,E_bind,input_erase seeds y (a::l) a hlater']
    calc
      _ = ∑ y : Tbl P, (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ *
          E (run (hash (Record.input (seeds,y) a)) (c y)) (K y) :=
        Finset.sum_congr rfl fun y _ => by rw [hstep]
      _ = ∑ y : Tbl P, (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ *
          K y (y a,ch y) := by
        exact avg_hash a (fun y => Record.input (seeds,y) a) c K
          (fun y => freshLocs_hash hP seeds y (a::l) (c y) (hfr y) a (by simp))
          (fun y v => Record.input_update seeds y a a v (earlier_irrefl a))
          (fun y v => hu y a (by simp) v)
          (fun y v p => by dsimp only [K]; rw [erase_update_mem y (a::l) a (by simp) v])
      _ = ∑ y : Tbl P, (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ *
          E (run (P.evalLocations seeds l (erase y l)) (ch y)) F := by
        refine Finset.sum_congr rfl fun y _ => ?_
        dsimp only [K]
        rw [update_erase_cons y a l hna]
      _ = ∑ y : Tbl P, (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ *
          F (y,progUpd (seeds,y) (fun b => b ∈ l) (ch y)) := ih htail ch hfr' hu' F
      _ = _ := by
        refine Finset.sum_congr rfl fun y _ => ?_
        dsimp only [ch]
        rw [progUpd_cacheQuery hP]
        rw [progUpd_congr (show ∀ b, (b ∈ l ∨ b = a) ↔ b ∈ a::l by simp [or_comm])]

/-- Erasing every location gives the actual initial table of key generation. -/
theorem erase_all (P : Params) (y : Tbl P) : erase y P.locationOrder = fun _ => 0 := by
  funext a
  exact if_pos (P.locationOrder_mem a)

theorem E_run_locations_full (hP : P.Hyp) (hl : P.locationOrder.Pairwise Earlier)
    (seeds : Fin 42 → Word) (F : Tbl P × Cache → ℝ≥0∞) :
    E (run (P.evalLocations seeds P.locationOrder (fun _ => 0)) ∅) F =
      ∑ y : Tbl P, (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ * F (y,Record.cache (seeds,y)) := by
  have h := E_evalLocations_avg hP seeds P.locationOrder hl (fun _ => ∅)
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl) F
  simp only [erase_all] at h
  rw [sum_inv_card_mul'] at h
  refine h.trans ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [progUpd_congr (show ∀ a, a ∈ P.locationOrder ↔ True from
    fun a => ⟨fun _ => trivial,fun _ => P.locationOrder_mem a⟩),progUpd_true_empty hP]

theorem E_run_keygen_seeds (hP : P.Hyp) (hl : P.locationOrder.Pairwise Earlier)
    (seeds : Fin 42 → Word) (G : (PublicKey × SecretKey) × Cache → ℝ≥0∞) :
    E (run (P.evalLocations seeds P.locationOrder (fun _ => 0) >>= fun y =>
      pure (Record.pk (seeds,y),Record.sk (seeds,y))) ∅) G =
      ∑ y : Tbl P, (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ *
        G ((Record.pk (seeds,y),Record.sk (seeds,y)),Record.cache (seeds,y)) := by
  rw [run_bind,E_bind]
  simp only [run_pure,E_pure]
  exact E_run_locations_full hP hl seeds (fun p => G ((Record.pk (seeds,p.1),Record.sk (seeds,p.1)),p.2))

/-- Key generation is exactly a uniform record under the shared lazy random oracle. -/
theorem E_run_keygen (hP : P.Hyp) (hl : P.locationOrder.Pairwise Earlier)
    (G : (PublicKey × SecretKey) × Cache → ℝ≥0∞) :
    E (run P.keygen ∅) G = ∑ ξ : Record P, recW P * G ((ξ.pk,ξ.sk),ξ.cache) := by
  have h0 : (Fintype.card (Fin 42 → Word) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ht : (Fintype.card (Fin 42 → Word) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcard : recW P = (Fintype.card (Fin 42 → Word) : ℝ≥0∞)⁻¹ *
      (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ := by
    rw [recW,Fintype.card_prod,Nat.cast_mul,ENNReal.mul_inv (Or.inl h0) (Or.inl ht)]
  calc
    _ = ∑ seeds : Fin 42 → Word, (Fintype.card (Fin 42 → Word) : ℝ≥0∞)⁻¹ *
        E (run (P.evalLocations seeds P.locationOrder (fun _ => 0) >>= fun y =>
          pure (Record.pk (seeds,y),Record.sk (seeds,y))) ∅) G := by
      rw [Params.keygen,run_bind,E_bind,E_run_tabulate_sample]
    _ = ∑ seeds : Fin 42 → Word, (Fintype.card (Fin 42 → Word) : ℝ≥0∞)⁻¹ *
        ∑ y : Tbl P, (Fintype.card (Tbl P) : ℝ≥0∞)⁻¹ *
          G ((Record.pk (seeds,y),Record.sk (seeds,y)),Record.cache (seeds,y)) :=
      Finset.sum_congr rfl fun seeds _ => by rw [E_run_keygen_seeds hP hl]
    _ = ∑ seeds : Fin 42 → Word, ∑ y : Tbl P, recW P *
        G ((Record.pk (seeds,y),Record.sk (seeds,y)),Record.cache (seeds,y)) := by
      refine Finset.sum_congr rfl fun seeds _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hcard,mul_assoc]
    _ = _ := (Fintype.sum_prod_type (fun ξ : Record P => recW P * G ((ξ.pk,ξ.sk),ξ.cache))).symm

end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
