import ProphetSecretary.Statistics.FinitePriorPrefixSampling

/-!
# Actual conditional sampling law in a finite-prior experiment

The joint law retains the hidden atom while splitting the visible training
prefix from the independent ONLINE vector. Each atom has exactly its stated
product-instance law; the prior mixture need not make the online values and
hidden target independent.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ}

noncomputable def trainingOnlineLaw (F : FinitePrior n) (c : ℕ) :
    Measure (Fin F.size × (((Fin n × Fin c) → ℝ) × (Fin n → ℝ))) :=
  ∑ θ : Fin F.size, F.weight θ • (Measure.dirac θ).prod
    (((F.offerInstance θ).trainingCoordinateLaw c).prod (F.offerInstance θ).valuesLaw)

def trainingOnlineObservation (F : FinitePrior n) (N c : ℕ) (hc : c≤N) (ω : BaseWorld F N) :
    Fin F.size × (((Fin n × Fin c) → ℝ) × (Fin n → ℝ)) :=
  (ω.1,prefixOnlineValues n N c hc ω.2)

lemma trainingOnlineObservation_measurePreserving (F : FinitePrior n) (N c : ℕ) (hc : c≤N) :
    MeasurePreserving (F.trainingOnlineObservation N c hc) (F.law N) (F.trainingOnlineLaw c) := by
  have hAtom (θ : Fin F.size) : MeasurePreserving (F.trainingOnlineObservation N c hc)
      (F.atomLaw N θ) ((Measure.dirac θ).prod
        (((F.offerInstance θ).trainingCoordinateLaw c).prod (F.offerInstance θ).valuesLaw)) :=
    (MeasurePreserving.id (Measure.dirac θ)).prod
      (prefixOnlineValues_measurePreserving (F.offerInstance θ) N c hc)
  have hm : Measurable (F.trainingOnlineObservation N c hc) :=
    measurable_fst.prodMk ((measurable_pi_lambda _ (fun q => (measurable_pi_apply _).comp measurable_snd)).prodMk
      (measurable_pi_lambda _ (fun i => (measurable_pi_apply (i,Fin.last N)).comp measurable_snd)))
  refine ⟨hm,?_⟩
  simp only [law,trainingOnlineLaw,Measure.map_finset_sum' hm.aemeasurable,Measure.map_smul]
  exact Finset.sum_congr rfl fun θ _ => congrArg (fun μ => F.weight θ • μ) (hAtom θ).map_eq

end ProphetSecretary.Statistics.FinitePrior
