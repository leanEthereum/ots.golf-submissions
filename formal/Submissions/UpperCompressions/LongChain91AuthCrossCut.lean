import Submissions.UpperCompressions.LongChain91AuthGame

/-!
# Cross-cut authentication for the cost-90 shared-DAG construction

Every scheduled cut has reconstruction cost 89, so two distinct scheduled cuts
differ at a hash node `u` that the forged cut reconstructs and the signed cut
does not (`exists_hidden_of_ne`).  The descent of
`LongChain91AuthClosure` gives either a spurious binding or the honest input
of `u`, which is a hidden key-generation point of the signed cut.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag
open Name

/-! ## The cross-cut event -/

theorem events_ne {A A' : Finset Name} (hA : IsCut A) (hA' : IsCut A')
    (hne : A ≠ A') {xi : Rec} {d : Cache}
    {given y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A') given y)
    (hacc : lowPk (yv y Name.rh) = pkOf xi) :
    Spr d xi ∨ Cache.Hits d (fHid (some A) xi) := by
  obtain ⟨c, hc, rfl⟩ := hA
  obtain ⟨c', hc', rfl⟩ := hA'
  obtain ⟨u, huE', huE, hu, -⟩ := exists_hidden_of_ne hc hc' hne
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 ((hashParent_isSome_iff u).2 hu)
  rcases descent_query ⟨c', hc', rfl⟩ hy hacc hp huE' with hs | hq
  · exact Or.inl hs
  · right
    refine ⟨pointOf xi u p, ?_, hq⟩
    rw [fHid_isSome_some_iff]
    exact ⟨u, p, hp, huE, rfl⟩

theorem crossCutAuthentication : CrossCutAuthentication := by
  intro xi signedClass i d given y hic hy hacc
  have hA := isCut_of_mem_family (setsName_mem signedClass)
  have hA' := isCut_of_mem_family (setsName_mem i)
  exact events_ne hA hA'
    (fun he => hic (setsName_injective he.symm)) hy hacc

theorem accepted_class_cases_actual
    (xi : Rec) (signedClass : Fin M) (m : Message)
    (sigma : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (scheme.verify (pkOf xi) m sigma) c)) :
    ∃ answer, d (encQuery (m, sigma.1)) = some answer ∧
      ∃ i : Fin M, LongChain91Schedule.decode answer = some i ∧
        ((i = signedClass ∧
            sigma.2 = graph.encode (fins (setsName signedClass))
              (graph.evalRec xi)) ∨
          Spr d xi ∨
          Cache.Hits d (fHid (some (setsName signedClass)) xi)) :=
  accepted_class_cases crossCutAuthentication xi signedClass m sigma c d h

theorem accepted_strong_event_actual
    (xi : Rec) (signedClass : Fin M) (signedInput : EncInput)
    (m : Message) (sigma : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (scheme.verify (pkOf xi) m sigma) c))
    (hne : (m, sigma) ≠ (signedInput.1,
      (signedInput.2,
        graph.encode (fins (setsName signedClass)) (graph.evalRec xi)))) :
    Spr d xi ∨ Cache.Hits d (fHid (some (setsName signedClass)) xi) ∨
      AlternateClass d signedInput signedClass :=
  accepted_strong_event crossCutAuthentication xi signedClass signedInput
    m sigma c d h hne

#print axioms events_ne
#print axioms crossCutAuthentication
#print axioms accepted_strong_event_actual

end OptimalOTS.WeightedConstruction.LongChain91
