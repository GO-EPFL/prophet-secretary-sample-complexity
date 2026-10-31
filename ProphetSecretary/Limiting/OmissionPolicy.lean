import ProphetSecretary.Limiting.OmissionHistories
import ProphetSecretary.Limiting.CountableScalarObjectives
import ProphetSecretary.Limiting.CountableCloudSplit

/-!
# The actual causal omission simulator

Omitted individual values/clocks and the independent low cloud are auxiliary
randomness. Original callbacks see only their reconstructed strict past. A
retained acceptance is allowed only above reserve, ensuring reward at least
reserve without deleting the observed histories of zero or low arrivals.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

abbrev OmissionAux (Seed : Type*) := (Seed × Measure Point) × ((ℕ → ℝ) × (ℕ → ℝ))

noncomputable def simulateOmittedRule (B : CountableInstance) {Seed : Type*}
    (π : CountableRule Seed) (N : ℕ) : HybridRule N (OmissionAux Seed) where
  individual s t i x H ξ := if (B.terminal : ℝ) < x then
    π.individual s.1.1 t i.val x (augmentIndividualHistory N H s.2.1 s.2.2 t)
      (ξ + omittedCloudPast B s.1.2 t) else false
  poisson s t x H ξ := if (B.terminal : ℝ) < x then
    π.poisson s.1.1 t x (augmentIndividualHistory N H s.2.1 s.2.2 t)
      (ξ + omittedCloudPast B s.1.2 t) else false

abbrev OmissionIndividualInput (N : ℕ) (Seed : Type*) :=
  OmissionAux Seed × (ℝ × (Fin N × (ℝ × (Model.History N × Measure Point))))
abbrev OmissionPoissonInput (N : ℕ) (Seed : Type*) :=
  OmissionAux Seed × (Point × (Model.History N × Measure Point))

lemma simulateOmittedRule_measurable (B : CountableInstance) {Seed : Type*} [MeasurableSpace Seed]
    (π : CountableRule Seed) (hπ : π.IsMeasurable) (N : ℕ) : (simulateOmittedRule B π N).IsMeasurable := by
  constructor
  · have hr : Measurable (fun q : OmissionIndividualInput N Seed => q.1.1.1) := by fun_prop
    have ht : Measurable (fun q : OmissionIndividualInput N Seed => q.2.1) := by fun_prop
    have hi : Measurable (fun q : OmissionIndividualInput N Seed => q.2.2.1.val) := by fun_prop
    have hx : Measurable (fun q : OmissionIndividualInput N Seed => q.2.2.2.1) := by fun_prop
    have hH : Measurable (fun q : OmissionIndividualInput N Seed =>
        augmentIndividualHistory N q.2.2.2.2.1 q.1.2.1 q.1.2.2 q.2.1) :=
      measurable_augmentIndividualHistory (by fun_prop) (by fun_prop) (by fun_prop) ht
    have hlow : Measurable (fun q : OmissionIndividualInput N Seed => q.1.1.2) := by fun_prop
    have hhigh : Measurable (fun q : OmissionIndividualInput N Seed => q.2.2.2.2.2) := by fun_prop
    have hcloud : Measurable (fun q : OmissionIndividualInput N Seed => omittedCloudPast B q.1.1.2 q.2.1) :=
      measurable_omittedCloudPast_family B hlow ht
    have hξ : Measurable (fun q : OmissionIndividualInput N Seed =>
        q.2.2.2.2.2 + omittedCloudPast B q.1.1.2 q.2.1) := hhigh.add hcloud
    exact Measurable.ite (measurableSet_lt measurable_const hx)
      (hπ.1.comp (hr.prodMk (ht.prodMk (hi.prodMk (hx.prodMk (hH.prodMk hξ)))))) measurable_const
  · have hr : Measurable (fun q : OmissionPoissonInput N Seed => q.1.1.1) := by fun_prop
    have ht : Measurable (fun q : OmissionPoissonInput N Seed => q.2.1.1) := by fun_prop
    have hx : Measurable (fun q : OmissionPoissonInput N Seed => q.2.1.2) := by fun_prop
    have hH : Measurable (fun q : OmissionPoissonInput N Seed =>
        augmentIndividualHistory N q.2.2.1 q.1.2.1 q.1.2.2 q.2.1.1) :=
      measurable_augmentIndividualHistory (by fun_prop) (by fun_prop) (by fun_prop) ht
    have hlow : Measurable (fun q : OmissionPoissonInput N Seed => q.1.1.2) := by fun_prop
    have hhigh : Measurable (fun q : OmissionPoissonInput N Seed => q.2.2.2) := by fun_prop
    have hcloud : Measurable (fun q : OmissionPoissonInput N Seed => omittedCloudPast B q.1.1.2 q.2.1.1) :=
      measurable_omittedCloudPast_family B hlow ht
    have hξ : Measurable (fun q : OmissionPoissonInput N Seed =>
        q.2.2.2 + omittedCloudPast B q.1.1.2 q.2.1.1) := hhigh.add hcloud
    exact Measurable.ite (measurableSet_lt measurable_const hx)
      (hπ.2.comp (hr.prodMk ((ht.prodMk hx).prodMk (hH.prodMk hξ)))) measurable_const

noncomputable def CountableInstance.lowCloudLaw (B : CountableInstance) (b : ℝ) : Measure (Measure Point) :=
  B.bandConfigurationsLaw.map (fun ω => (bandCountingMeasure ω).restrict (univ ×ˢ Ioc (B.terminal : ℝ) b))

lemma CountableInstance.measurable_lowCloud (B : CountableInstance) (b : ℝ) :
    Measurable (fun ω : BandConfigurations => (bandCountingMeasure ω).restrict (univ ×ˢ Ioc (B.terminal : ℝ) b)) :=
  (measurable_measureRestriction (MeasurableSet.univ.prod measurableSet_Ioc)).comp measurable_bandCountingMeasure

instance CountableInstance.lowCloudLaw_probability (B : CountableInstance) (b : ℝ) :
    IsProbabilityMeasure (B.lowCloudLaw b) :=
  Measure.isProbabilityMeasure_map (B.measurable_lowCloud b).aemeasurable

noncomputable def RandomizedCountablePolicy.simulateOmissions {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (N : ℕ) (b : ℝ) : RandomizedHybridPolicy N where
  Seed := OmissionAux π.Seed
  seedLaw := (π.seedLaw.prod (B.lowCloudLaw b)).prod ((B.tailValuesLaw N).prod individualClocksLaw)
  rule := simulateOmittedRule B π.rule N
  measurable_rule := simulateOmittedRule_measurable B π.rule π.measurable_rule N

end ProphetSecretary.Limiting
