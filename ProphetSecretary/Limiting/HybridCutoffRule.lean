import ProphetSecretary.Limiting.HybridAcceptedMeasure

/-!
# A causal hybrid rule ignoring anonymous marks below a cutoff

Retained zero-valued identities are preserved. Anonymous callbacks receive
only the strict past restricted above the cutoff; a low current anonymous
mark is rejected. Neither callback receives the future point configuration.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*}

noncomputable def HybridRule.above (π : HybridRule n Seed) (b : ℝ) : HybridRule n Seed where
  individual r t i x H ξ := π.individual r t i x H (ξ.restrict (univ ×ˢ Ioi b))
  poisson r t x H ξ := if b<x then π.poisson r t x H (ξ.restrict (univ ×ˢ Ioi b)) else false

lemma HybridRule.above_measurable [MeasurableSpace Seed]
    (π : HybridRule n Seed) (hπ : π.IsMeasurable) (b : ℝ) : (π.above b).IsMeasurable := by
  constructor
  · have hM : Measurable (fun q : Seed × (ℝ × (Fin n × (ℝ × (Model.History n × Measure Point)))) => q.2.2.2.2.2.restrict (univ ×ˢ Ioi b)) :=
      (measurable_measureRestriction (MeasurableSet.univ.prod measurableSet_Ioi)).comp (by fun_prop)
    exact hπ.1.comp ((by fun_prop : Measurable (fun q : Seed × (ℝ × (Fin n × (ℝ × (Model.History n × Measure Point)))) => q.1)).prodMk
      ((by fun_prop : Measurable (fun q : Seed × (ℝ × (Fin n × (ℝ × (Model.History n × Measure Point)))) => q.2.1)).prodMk
      ((by fun_prop : Measurable (fun q : Seed × (ℝ × (Fin n × (ℝ × (Model.History n × Measure Point)))) => q.2.2.1)).prodMk
      ((by fun_prop : Measurable (fun q : Seed × (ℝ × (Fin n × (ℝ × (Model.History n × Measure Point)))) => q.2.2.2.1)).prodMk
      ((by fun_prop : Measurable (fun q : Seed × (ℝ × (Fin n × (ℝ × (Model.History n × Measure Point)))) => q.2.2.2.2.1)).prodMk hM)))))
  · have hM : Measurable (fun q : Seed × (Point × (Model.History n × Measure Point)) => q.2.2.2.restrict (univ ×ˢ Ioi b)) :=
      (measurable_measureRestriction (MeasurableSet.univ.prod measurableSet_Ioi)).comp (by fun_prop)
    have hComp := hπ.2.comp ((by fun_prop : Measurable (fun q : Seed × (Point × (Model.History n × Measure Point)) => q.1)).prodMk
      (((by fun_prop : Measurable (fun q : Seed × (Point × (Model.History n × Measure Point)) => q.2.1.1)).prodMk
        (by fun_prop : Measurable (fun q : Seed × (Point × (Model.History n × Measure Point)) => q.2.1.2))).prodMk
      ((by fun_prop : Measurable (fun q : Seed × (Point × (Model.History n × Measure Point)) => q.2.2.1)).prodMk hM)))
    exact Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) hComp measurable_const

noncomputable def configurationAbove (b : ℝ) (ω : Configuration) : FiniteMeasure Point :=
  ProphetSecretary.Probability.finiteMeasureOrZero ((countingMeasure ω).restrict (univ ×ˢ Ioi b))

lemma configurationAbove_coe (b : ℝ) (ω : Configuration) :
    (configurationAbove b ω : Measure Point) = (countingMeasure ω).restrict (univ ×ˢ Ioi b) := by
  apply ProphetSecretary.Probability.finiteMeasureOrZero_coe
  unfold countingMeasure
  infer_instance

lemma measurable_configurationAbove (b : ℝ) : Measurable (configurationAbove b) :=
  ProphetSecretary.Probability.measurable_finiteMeasureOrZero.comp
    ((measurable_measureRestriction (MeasurableSet.univ.prod measurableSet_Ioi)).comp measurable_countingMeasure)

lemma configurationAbove_past (b : ℝ) (ω : Configuration) (t : ℝ) :
    finitePast (configurationAbove b ω) t = (observedHistory ω t).restrict (univ ×ˢ Ioi b) := by
  rw [finitePast,configurationAbove_coe,observedHistory_eq_countingRestriction]
  rw [Measure.restrict_restrict (measurableSet_Iio.prod MeasurableSet.univ),
    Measure.restrict_restrict (MeasurableSet.univ.prod measurableSet_Ioi)]
  congr 1
  exact inter_comm _ _

noncomputable def hybridObserverAbove (b : ℝ) (v : HybridWorld n Seed) : FiniteObserverWorld n Seed :=
  (configurationAbove b v.1,v.2)

lemma HybridRule.individualMeasureAction_above (π : HybridRule n Seed) (b : ℝ)
    (v : HybridWorld n Seed) (i : Fin n) :
    π.individualMeasureAction (hybridObserverAbove b v) i =
      ((π.above b).asFinitePolicy v.1.1).action v.2.2.2 Finset.univ
        (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) (i.castAdd v.1.1) := by
  rw [HybridRule.individual_action]
  change π.individual v.2.2.2 (v.2.2.1 i) i (v.2.1 i)
    (Model.history Finset.univ v.2.1 v.2.2.1 (v.2.2.1 i))
    (finitePast (configurationAbove b v.1) (v.2.2.1 i)) = _
  rw [configurationAbove_past]
  rcases v with ⟨⟨N,pts⟩,q⟩
  rfl

lemma HybridRule.anonymousMeasureAction_above (π : HybridRule n Seed) (b : ℝ)
    (v : HybridWorld n Seed) (j : Fin v.1.1) :
    ((π.above b).asFinitePolicy v.1.1).action v.2.2.2 Finset.univ
        (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) (j.natAdd n) =
      if b<(v.1.2 j).2 then π.anonymousMeasureAction (hybridObserverAbove b v) (v.1.2 j) else false := by
  rw [HybridRule.poisson_action]
  change (if b<(v.1.2 j).2 then π.poisson v.2.2.2 (v.1.2 j).1 (v.1.2 j).2
    (Model.history Finset.univ v.2.1 v.2.2.1 (v.1.2 j).1)
    ((observedHistory v.1 (v.1.2 j).1).restrict (univ ×ˢ Ioi b)) else false) = _
  rw [← configurationAbove_past]
  rfl
end ProphetSecretary.Limiting
