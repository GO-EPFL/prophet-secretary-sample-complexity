import ProphetSecretary.Limiting.FiniteObserverLaw
import ProphetSecretary.Limiting.AcceptedPointSums

/-!
# The finite hybrid execution's actual accepted-point measure

Every retained and anonymous action agrees with the callback supplied the
counting-measure strict past. The resulting measure includes all analytical
acceptances but supplies no count or future observations to a decision rule.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*}

noncomputable def hybridObserverWorld (v : HybridWorld n Seed) : FiniteObserverWorld n Seed :=
  (configurationFiniteMeasure v.1,v.2)

lemma configurationFinitePast (ω : Configuration) (t : ℝ) :
    finitePast (configurationFiniteMeasure ω) t = observedHistory ω t := by
  rw [finitePast,configurationFiniteMeasure_coe,observedHistory_eq_countingRestriction]

lemma HybridRule.individualMeasureAction_eq_adapter (π : HybridRule n Seed) (v : HybridWorld n Seed) (i : Fin n) :
    π.individualMeasureAction (hybridObserverWorld v) i =
      (π.asFinitePolicy v.1.1).action v.2.2.2 Finset.univ (combinedValues v.2.1 v.1.2)
        (combinedClocks v.2.2.1 v.1.2) (i.castAdd v.1.1) := by
  rw [HybridRule.individual_action]
  change π.individual v.2.2.2 (v.2.2.1 i) i (v.2.1 i)
    (Model.history Finset.univ v.2.1 v.2.2.1 (v.2.2.1 i))
    (finitePast (configurationFiniteMeasure v.1) (v.2.2.1 i)) = _
  rw [configurationFinitePast]
  rcases v with ⟨⟨K,pts⟩,q⟩
  rfl

lemma HybridRule.anonymousMeasureAction_eq_adapter (π : HybridRule n Seed) (v : HybridWorld n Seed)
    (j : Fin v.1.1) :
    π.anonymousMeasureAction (hybridObserverWorld v) (v.1.2 j) =
      (π.asFinitePolicy v.1.1).action v.2.2.2 Finset.univ (combinedValues v.2.1 v.1.2)
        (combinedClocks v.2.2.1 v.1.2) (j.natAdd n) := by
  rw [HybridRule.poisson_action]
  change π.poisson v.2.2.2 (v.1.2 j).1 (v.1.2 j).2
    (Model.history Finset.univ v.2.1 v.2.2.1 (v.1.2 j).1)
    (finitePast (configurationFiniteMeasure v.1) (v.1.2 j).1) = _
  rw [configurationFinitePast]
  rcases v with ⟨⟨K,pts⟩,q⟩
  rfl

variable [MeasurableSpace Seed]

lemma HybridRule.acceptedPointMeasure_eq_adapter (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (v : HybridWorld n Seed) :
    (π.acceptedPointMeasure (hybridObserverWorld v) : Measure Point) =
      ∑ k : Fin (n+v.1.1), if combinedClocks v.2.2.1 v.1.2 k ∈ Icc (0 : ℝ) 1 ∧
        (π.asFinitePolicy v.1.1).action v.2.2.2 Finset.univ (combinedValues v.2.1 v.1.2)
          (combinedClocks v.2.2.1 v.1.2) k = true then
        Measure.dirac (combinedClocks v.2.2.1 v.1.2 k,combinedValues v.2.1 v.1.2 k) else 0 := by
  have hA : MeasurableSet {p : Point | π.anonymousMeasureAccepted (hybridObserverWorld v) p} :=
    (π.measurableSet_anonymousMeasureAccepted hπ).preimage measurable_prodMk_left
  change (∑ i : Fin n, if π.individualMeasureAccepted (hybridObserverWorld v) i then
    Measure.dirac (v.2.2.1 i,v.2.1 i) else 0) +
    (configurationFiniteMeasure v.1 : Measure Point).restrict
      {p | π.anonymousMeasureAccepted (hybridObserverWorld v) p} = _
  rw [configurationFiniteMeasure_coe,restricted_countingMeasure _ hA,Fin.sum_univ_add]
  apply congrArg₂ (fun α β : Measure Point => α + β)
  · apply Finset.sum_congr rfl
    intro i _
    simp only [combinedClocks,combinedValues,Fin.addCases_left,HybridRule.individualMeasureAccepted]
    simp only [π.individualMeasureAction_eq_adapter v i]
    rfl
  · apply Finset.sum_congr rfl
    intro j _
    simp only [combinedClocks,combinedValues,Fin.addCases_right,mem_setOf_eq,HybridRule.anonymousMeasureAccepted]
    simp only [π.anonymousMeasureAction_eq_adapter v j]

end ProphetSecretary.Limiting
