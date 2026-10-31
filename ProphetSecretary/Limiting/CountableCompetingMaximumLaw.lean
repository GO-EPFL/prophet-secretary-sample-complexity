import ProphetSecretary.Limiting.CountableCompetingMaximum
import Mathlib.Probability.HasLaw

/-!
# The competing maximum law and exact benchmark factorization

The law is defined on the value space, independently of clocks and policy
randomness. Actual product erasure identifies its joint law with the chosen
individual as the product of their marginals. Fubini then expresses the
prophet benchmark through the two-variable maximum kernel.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def competingValueMaximum (B : CountableInstance) (i : ℕ) (v : ValueWorld) : ℝ :=
  B.maximum (v.1,Function.update v.2 i 0)

lemma measurable_competingValueMaximum (B : CountableInstance) (i : ℕ) :
    Measurable (B.competingValueMaximum i) :=
  B.measurable_maximum.comp (measurable_fst.prodMk
    ((Model.measurable_eraseCoordinate i (0 : ℝ)).comp measurable_snd))

noncomputable def competingMaximumLaw (B : CountableInstance) (i : ℕ) : ProbabilityMeasure ℝ :=
  ⟨Measure.map (B.competingValueMaximum i) B.valueLaw,
    B.valueLaw.isProbabilityMeasure_map (B.measurable_competingValueMaximum i).aemeasurable⟩

theorem competingMaximum_hasLaw (B : CountableInstance) (i : ℕ)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    HasLaw (B.competingMaximum i) (B.competingMaximumLaw i : Measure ℝ) (B.completeWorldLaw ν) := by
  have hProjection := B.value_projection_measurePreserving ν
  refine ⟨(B.measurable_competingMaximum i).aemeasurable,?_⟩
  change Measure.map (B.competingMaximum i) (B.completeWorldLaw ν)=
    Measure.map (B.competingValueMaximum i) B.valueLaw
  rw [← hProjection.map_eq,Measure.map_map (B.measurable_competingValueMaximum i) hProjection.measurable]
  rfl

theorem competingMaximum_bounded_ae (B : CountableInstance) (i : ℕ)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂B.completeWorldLaw ν, B.competingMaximum i v ∈ Icc (0 : ℝ) B.cap := by
  filter_upwards [B.maximum_replaceIndividual_eq_max_ae ν i,B.maximum_eq_max_competing_ae ν i,
    (B.value_projection_measurePreserving ν).quasiMeasurePreserving.ae B.maximum_bounded]
    with v hReplace hActual hBound
  have hZero := hReplace 0
  change B.competingMaximum i v=max 0 (B.competingMaximum i v) at hZero
  exact ⟨(le_max_left _ _).trans_eq hZero.symm,((le_max_right _ _).trans_eq hActual.symm).trans hBound.2⟩

theorem competingMaximumLaw_supported (B : CountableInstance) (i : ℕ) :
    ∀ᵐ y ∂(B.competingMaximumLaw i : Measure ℝ), y ∈ Icc (0 : ℝ) B.cap := by
  have hLaw := B.competingMaximum_hasLaw i (Measure.dirac ())
  rw [← hLaw.map_eq]
  exact (ae_map_iff hLaw.aemeasurable measurableSet_Icc).mpr (B.competingMaximum_bounded_ae i (Measure.dirac ()))

lemma competingMaximumLaw_integrable (B : CountableInstance) (i : ℕ) :
    Integrable id (B.competingMaximumLaw i : Measure ℝ) := by
  apply Integrable.of_bound measurable_id.aestronglyMeasurable (B.cap : ℝ)
  filter_upwards [B.competingMaximumLaw_supported i] with y hy
  change ‖y‖ ≤ (B.cap : ℝ)
  rw [Real.norm_eq_abs,abs_of_nonneg hy.1]
  exact hy.2

theorem individual_competingMaximum_jointLaw (B : CountableInstance) (i : ℕ)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    HasLaw (fun v : CompleteWorld Seed => (v.2.1 i,B.competingMaximum i v))
      ((B.individuals i : Measure ℝ).prod (B.competingMaximumLaw i : Measure ℝ)) (B.completeWorldLaw ν) := by
  have hXi : MeasurePreserving (fun v : CompleteWorld Seed => v.2.1 i)
      (B.completeWorldLaw ν) (B.individuals i : Measure ℝ) :=
    (B.individualValue_measurePreserving i).comp (measurePreserving_fst.comp measurePreserving_snd)
  exact (B.competingMaximum_independent_value ν i).symm.hasLaw_prod hXi.hasLaw (B.competingMaximum_hasLaw i ν)

lemma individual_competingMaximum_product_integrable (B : CountableInstance) (i : ℕ) :
    Integrable (fun z : ℝ × ℝ => max z.1 z.2)
      ((B.individuals i : Measure ℝ).prod (B.competingMaximumLaw i : Measure ℝ)) := by
  have hLeft := (Measure.quasiMeasurePreserving_fst (μ := (B.individuals i : Measure ℝ))
    (ν := (B.competingMaximumLaw i : Measure ℝ))).ae (B.individual_supported i)
  have hRight := (Measure.quasiMeasurePreserving_snd (μ := (B.individuals i : Measure ℝ))
    (ν := (B.competingMaximumLaw i : Measure ℝ))).ae (B.competingMaximumLaw_supported i)
  apply Integrable.of_bound (measurable_fst.max measurable_snd).aestronglyMeasurable (B.cap : ℝ)
  filter_upwards [hLeft,hRight] with z hz hq
  rw [Real.norm_eq_abs,abs_of_nonneg (hz.1.trans (le_max_left _ _))]
  exact max_le hz.2 hq.2

theorem expectedMaximum_eq_individual_competing_kernel (B : CountableInstance) (i : ℕ) :
    B.expectedMaximum=∫ x, (∫ y, max x y ∂(B.competingMaximumLaw i : Measure ℝ)) ∂(B.individuals i : Measure ℝ) := by
  have hValue := (B.value_projection_measurePreserving (Measure.dirac ())).hasLaw.integral_comp B.measurable_maximum.aestronglyMeasurable
  have hPair := (B.individual_competingMaximum_jointLaw i (Measure.dirac ())).integral_comp
    (measurable_fst.max measurable_snd).aestronglyMeasurable
  calc
    _ = ∫ v : CompleteWorld Unit, B.maximum (v.1,v.2.1) ∂B.completeWorldLaw (Measure.dirac ()) := hValue.symm
    _ = ∫ v : CompleteWorld Unit, max (v.2.1 i) (B.competingMaximum i v) ∂B.completeWorldLaw (Measure.dirac ()) :=
      integral_congr_ae (B.maximum_eq_max_competing_ae (Measure.dirac ()) i)
    _ = ∫ z : ℝ × ℝ, max z.1 z.2 ∂(B.individuals i : Measure ℝ).prod (B.competingMaximumLaw i : Measure ℝ) := hPair
    _ = _ := integral_prod _ (B.individual_competingMaximum_product_integrable i)

end ProphetSecretary.Limiting.CountableInstance
